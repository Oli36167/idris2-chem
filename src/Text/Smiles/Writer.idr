||| Writes a molecular graph (IGraph k SmilesBond SmilesAtom) out as a
||| SMILES string.
|||
||| Limitation: Currently only stereochemistry that is already explicitly
||| encoded in the graph is written into a SMILES string.
||| No stereochemistry is derived from atom coordinates.

module Text.Smiles.Writer

import Control.Monad.State

import Data.Graph.Indexed.Util
import Data.Graph.Indexed.Query.DFS
import Data.Tree

import Debug.Trace
import Decidable.Equality
import Derive.Prelude

import Text.Molfile.Types
import Text.Smiles.Parser
import Text.Smiles.Traversal
import Text.Smiles.Types


%default total
%language ElabReflection


--------------------------------------------------------------------------------
--          parity
--------------------------------------------------------------------------------
export
data Parity = Even | Odd

%runElab deriveIndexed "Parity" [Eq, Show]

export
Semigroup Parity where
  Even <+> p    = p
  Odd  <+> Even = Odd
  Odd  <+> Odd  = Even

export
Monoid Parity where
  neutral = Even

export
natToParity : Nat -> Parity
natToParity n =
  case mod n 2 of
    0 => Even
    _ => Odd

export
permutParity : Ord a => List a -> Parity
permutParity []        = natToParity 0
permutParity (x :: xs) = natToParity (count (< x) xs) <+> permutParity xs

isSameParity :
     List (ChiralNeighbour k)
  -> List (ChiralNeighbour k)
  -> Bool
isSameParity = (==) `on` permutParity

-- TODO what about all other cases?
invertChirality : Chirality -> Chirality
invertChirality CW  = CCW
invertChirality CCW = CW
invertChirality c   = c

invertChiralityData : ChiralityData -> ChiralityData
invertChiralityData (MkCD k ch ns) =  MkCD k (invertChirality ch) ns

accessSmilesAtom : SmilesAtom -> SmilesAtom
accessSmilesAtom (SubsetAtom elem arom) = SubsetAtom elem arom
accessSmilesAtom (Bracket atom) = Bracket atom

invertAtomChirality : SmilesAtom -> SmilesAtom
invertAtomChirality (SubsetAtom elem arom) = SubsetAtom elem arom
invertAtomChirality (Bracket atom) =
  Bracket $ { chirality := invertChiralityData atom.chirality } atom


findClosableOpenRing :
     {k : Nat}
  -> Fin k -- neighbour
  -> Fin k -- current
  -> List (RingData k)
  -> Maybe (RingData k)
findClosableOpenRing n c =
  find (\rd =>
    let e = edge rd in
    (node1 e == c && node2 e == n) ||
    (node1 e == n && node2 e == c))

allocateRingNr : List (RingData k) -> RingNr
allocateRingNr ors =
   fromMaybe 0 $
     find (\x => not (elem x (map ringNr ors)))
          (mapMaybe refineRingNr [1..99])

parameters {k : Nat}
           (g : IGraph k SmilesBond SmilesAtom)

  bothAromatic : Fin k -> Fin k -> Bool
  bothAromatic a b = isArom (lab g a) && isArom (lab g b)

  renderRingNrs : List (RingData k) -> String
  renderRingNrs =
    fastConcat . map render . sortBy (compare `on` ringNr)
    where
      render : RingData k -> String
      render rd@(RD e _) =
        let bothArom = bothAromatic (node1 e) (node2 e)
         in bondSymbol bothArom (label e) ++ interpolate (ringNr rd)

  renderTree : Tree (Node k) -> String
  renderTree (T c@(MkNode v _ _ rings) cs) =
    let rNr := renderRingNrs rings
     in "\{v}\{rNr}\{renderChildren cs}"
    where
      renderChildren : Forest (Node k) -> String
      renderChildren []               = ""
      renderChildren [h@(T c _)]      = renderBond c ++ renderTree h
      renderChildren (h@(T c _) :: t) =
        "(\{renderBond c}\{renderTree h})\{renderChildren t}"

  public export
  renderForest : Forest (Node k) -> String
  renderForest = fastConcat . intersperse "." . map renderTree

-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------
  -- rings = neighbours - parent - children
  computeNodeContext :
       Fin k
    -> Maybe (Fin k)
    -> Tree (Fin k)
    -> List (RingData k)
    -> List (RingData k)
  computeNodeContext c p (T _ ts) openR =
    foldl step openR filtered
    where
      filtered : List (Fin k, SmilesBond)
      filtered =
        let children = map value ts
        in filter
             (\(n, _) => not (elem n children) && not (Just n == p))
             (neighboursAsPairs g c)

      -- close an existing ring or open a new one
      step : List (RingData k) -> (Fin k, SmilesBond) -> List (RingData k)
      step ors (n, e) =
        case findClosableOpenRing n c ors of
          Just rd => filter (\r => ringNr r /= ringNr rd) ors
          Nothing =>
            maybe ors
                  (\edge => RD edge (R (allocateRingNr ors) Nothing) :: ors)
                  (mkEdge c n e)

  zipL : Forest (Fin k) -> State (NodeState k) (Forest (Node k))

  -- Rings that were opened or closed at this node.
  ringDelta : List (RingData k) -> List (RingData k) -> List (RingData k)
  ringDelta openR openR' =
    filter (not . flip elem openR') openR ++
    filter (not . flip elem openR ) openR'

  -- bond to parent (if any) and whether both atoms are aromatic
  parentInfo : Maybe (Fin k) -> Fin k -> (Maybe SmilesBond, Bool)
  parentInfo p v = (p >>= elab g v, maybe False (bothAromatic g v) p)

  updateParity :
       List (ChiralNeighbour k)
    -> List (ChiralNeighbour k)
    -> Fin k
    -> IGraph k SmilesBond SmilesAtom
  updateParity xs ys v =
    case isSameParity xs ys of
         True  => g
         -- graph darf nicht verändert werden
         False => updateNode v invertAtomChirality g

  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(MkNodeState p openR) <- get

    -- get info for current node
    let (openR', childrenAndRings) = computeNodeContext g v p t openR
        ringChanges    = ringDelta openR openR'
        initialNOrd    = initialNeighbourOrdering g v
        currentNOrd    = currentNeighbourOrdering g v p childrenAndRings
        -- refactor
        g'             = updateParity initialNOrd currentNOrd v
        nodeLabel      = lab g' v

    put (MkNodeState (Just v) openR') -- set current node as parent
    ts2 <- zipL ts           -- process children
    put pNS                  -- restore old parent

    let (pe, bothArom) = parentInfo p v

    pure (T (MkNode nodeLabel pe bothArom ringChanges) ts2)

  zipL []      = pure []
  zipL (t::ts) = [| buildNodeTree t :: zipL ts |]

  buildNodeForest : Forest (Fin k) -> Forest (Node k)
  buildNodeForest ts = evalState (MkNodeState Nothing []) (zipL ts)

export
graphToSmiles : {k : _} -> IGraph k SmilesBond SmilesAtom -> String
graphToSmiles g = renderForest g . buildNodeForest g $ dff' g


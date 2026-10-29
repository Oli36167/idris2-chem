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

import Derive.Prelude

import Text.Molfile.Types
import Text.Smiles.Parser
import Text.Smiles.Types

%default total
%language ElabReflection

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

record RingData k where
  constructor RD
  edge : Edge k SmilesBond
  ring : Ring

%runElab deriveIndexed "RingData" [Eq]

record Node k where
  constructor MkNode
  label : SmilesAtom
  parentEdge : Maybe SmilesBond
  bothArom : Bool
  rings : List (RingData k)

record NodeState k where
  constructor NS
  parent : Maybe (Fin k)
  openRings : List (RingData k)

%runElab deriveIndexed "NodeState" [Eq]

data ChiralNeighbour : Nat -> Type where
  ImpH     : ChiralNeighbour n
  Explicit : Fin n -> ChiralNeighbour n

%runElab deriveIndexed "ChiralNeighbour" [Show,Eq,Ord]

record ChildrenAndRings (k : Nat) where
  constructor CR
  children : List (Fin k)
  rings    : List (Fin k, SmilesBond)
--------------------------------------------------------------------------------
--          helpers
--------------------------------------------------------------------------------

getChildrenFinK : List (Tree (Fin k)) -> List (Fin k)
getChildrenFinK = map value

--------------------------------------------------------------------------------
--          lists
--------------------------------------------------------------------------------

-- TODO make PR for Data.List?
-- This exists for SetList but not List.
symDifference : Eq a => List a -> List a -> List a
symDifference xs ys = union (xs \\ ys) (ys \\ xs)

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

isSameParity : List (ChiralNeighbour k) -> List (ChiralNeighbour k) -> Bool
isSameParity = (==) `on` permutParity

-- TODO what about all other cases?
invertChirality : Chirality -> Chirality
invertChirality CW  = CCW
invertChirality CCW = CW
invertChirality c   = c

accessSmilesAtom : SmilesAtom -> SmilesAtom
accessSmilesAtom (SubsetAtom elem arom) = SubsetAtom elem arom
accessSmilesAtom (Bracket atom) = Bracket atom

invertAtomChirality : SmilesAtom -> SmilesAtom
invertAtomChirality (SubsetAtom elem arom) = SubsetAtom elem arom
invertAtomChirality (Bracket atom)         =
  Bracket $ { chirality := invertChirality atom.chirality } atom

------------------------------------------------------------------------------
-- SMILES Rendering
------------------------------------------------------------------------------

bondSymbol : Bool -> SmilesBond -> String
bondSymbol bothArom bo =
  if bo == (if bothArom then Arom else Sngl)
     then ""
     else interpolate bo

ringNr : RingData k -> RingNr
ringNr (RD _ (R nr _)) = nr

renderBond : Node k -> String
renderBond (MkNode _ pE bothArom _) = maybe "" (bondSymbol bothArom) pE

findClosableOpenRing :
     Fin k -- neighbour
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

  export
  renderForest : Forest (Node k) -> String
  renderForest = fastConcat . intersperse "." . map renderTree

--------------------------------------------------------------------------------
--          neighbours
--------------------------------------------------------------------------------

  initialNeighbourOrdering : Fin k -> List (ChiralNeighbour k)
  initialNeighbourOrdering v =
    case lab g v of
      (SubsetAtom elem arom) => []
      (Bracket atom)         => ?atomDOTneighbourList

  hasOneImplicitH : Fin k -> Bool
  hasOneImplicitH c =
    case lab g c of
      SubsetAtom elem arom => False
      Bracket atom         => case atom.hydrogen of
                                1 => True
                                _ => False

  ringNeighbours :
       Maybe (Fin k)
    -> Fin k
    -> List (Tree (Fin k))
    -> List (Fin k, SmilesBond)
  ringNeighbours p c ts =
    filter
    (\(n, _) => not (elem n (getChildrenFinK ts)) && not (Just n == p))
    (neighboursAsPairs g c)

  -- TODO make sure (with types) computeNodeContext uses the same funs
  -- (getChildrenFinK and ringNeighbours)
  currentNeighbourOrdering :
       Fin k
    -> Maybe (Fin k)
    -> ChildrenAndRings k
    -> List (ChiralNeighbour k)
  currentNeighbourOrdering c p (CR children rings) =
    let implicitH = if hasOneImplicitH c then [ImpH] else []
        parent    = maybe [] (pure . Explicit) p
        children'  = map Explicit children
        rings'     = map Explicit $ map fst $ rings
      in (parent ++ implicitH ++ children' ++ rings')
-------------------------------------------------------------------------------
-- Traversal Helpers
-------------------------------------------------------------------------------

  -- rings = neighbours - parent - children
  computeNodeContext :
       Fin k
    -> Maybe (Fin k)
    -> Tree (Fin k)
    -> List (RingData k)
    -> (List (RingData k), ChildrenAndRings k)
  computeNodeContext c p (T _ ts) openR =
    let children         = getChildrenFinK ts
        rings            = ringNeighbours p c ts
        context          = foldl step openR rings
        childrenAndRings = CR children rings
    in (context, childrenAndRings)
    where
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
  parentInfo p v = (p >>= elab g v, maybe False (bothAromatic v) p)

  updateParity :
       List (ChiralNeighbour k)
    -> List (ChiralNeighbour k)
    -> Fin k
    -> IGraph k SmilesBond SmilesAtom
  updateParity xs ys v =
    case isSameParity xs ys of
         True  => g
         False => updateNode v invertAtomChirality g

  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(NS p openR) <- get

    -- get info for current node
    let (openR', childrenAndRings) = computeNodeContext v p t openR
        ringChanges    = ringDelta openR openR'
        initialNOrd    = initialNeighbourOrdering v
        currentNOrd    = currentNeighbourOrdering v p childrenAndRings
        g'             = updateParity initialNOrd currentNOrd v
        nodeLabel      = lab g' v

    put (NS (Just v) openR') -- set current node as parent
    ts2 <- zipL ts           -- process children
    put pNS                  -- restore old parent

    let (pe, bothArom) = parentInfo p v

    pure (T (MkNode nodeLabel pe bothArom ringChanges) ts2)

  zipL []      = pure []
  zipL (t::ts) = [| buildNodeTree t :: zipL ts |]

  buildNodeForest : Forest (Fin k) -> Forest (Node k)
  buildNodeForest ts = evalState (NS Nothing []) (zipL ts)

export
graphToSmiles : {k : _} -> IGraph k SmilesBond SmilesAtom -> String
graphToSmiles g = renderForest g . buildNodeForest g $ dff' g



||| This is WIP, use at your own risk.
||| Writes a molecular graph (IGraph k SmilesBondOrder SmilesAtom) out as a
||| SMILES string.
|||
||| Limitation: Currently only stereochemistry that is already explicitly
||| encoded in the graph is written into a SMILES string.
||| No stereochemistry is derived from atom coordinates.

module Text.Smiles.Writer

import Control.Monad.State
import Chem.Parity

import Data.Graph.Indexed.Util
import Data.Graph.Indexed.Query.DFS
import Data.Tree
import Derive.Prelude

import Text.Molfile.Types
import Text.Smiles.Parser
import Text.Smiles.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          parity
--------------------------------------------------------------------------------
-- TODO what about all other cases?
invertChirality : Chirality -> Chirality
invertChirality CW  = CCW
invertChirality CCW = CW
invertChirality c   = c

invertAtomChirality : SmilesAtom -> SmilesAtom
invertAtomChirality (SubsetAtom elem arom) = SubsetAtom elem arom
invertAtomChirality (Bracket atom) =
  Bracket $ { chirality := invertChirality atom.chirality } atom

updateChirality :
     List (BStereo k)
  -> List (BStereo k)
  -> SmilesAtom
  -> SmilesAtom
updateChirality xs ys atom =
  case sameParity xs ys of
    True  => atom
    False => invertAtomChirality atom

--------------------------------------------------------------------------------
--          helpers
--------------------------------------------------------------------------------

getChildrenFinK : {k : Nat} -> List (Tree (Fin k)) -> List (Fin k)
getChildrenFinK = map value

bondSymbol : Bool -> SmilesBond -> String
bondSymbol bothArom (SB _ o) =
  if o == (if bothArom then Arom else Sngl)
     then ""
     else interpolate o

export
ringNr : {k : Nat} -> RingData k -> RingNr
ringNr (RD _ (R nr _)) = nr

renderBond : {k : Nat} -> Node k -> String
renderBond (MkNode _ pE bothArom _) = maybe "" (bondSymbol bothArom) pE

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

allocateRingNr : {k : Nat} -> List (RingData k) -> RingNr
allocateRingNr ors =
   fromMaybe 0 $
     find (\x => not (elem x (map ringNr ors)))
          (mapMaybe refineRingNr [1..99])

-- TODO this was taken from test/src/Test/Text/Smiles/Stereo.idr
Cast SmilesAtom HCount where
  cast (SubsetAtom elem arom) = 0
  cast (Bracket x) = cast x

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

--------------------------------------------------------------------------------
--          neighbours
--------------------------------------------------------------------------------
  hasOneImplicitH : Fin k -> Bool
  hasOneImplicitH c =
    case lab g c of
      SubsetAtom elem arom => False
      Bracket atom         =>
        case atom.hydrogen of
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

-------------------------------------------------------------------------------
-- Traversal Helpers
-----------------------------------------------------------------------------

  currentNeighbourOrdering :
       Fin k
    -> Maybe (Fin k)
    -> ChildrenAndRings k
    -> List (BStereo k)
  currentNeighbourOrdering c p (CR children rings) =
    let implicitH = if hasOneImplicitH c then [ImpH] else []
        parent    = maybe [] (pure . Bnd) p
        children' = map Bnd children
        rings'    = map Bnd $ map fst $ rings
      in (parent ++ implicitH ++ children' ++ rings')

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


  buildNodeTree : Tree (Fin k) -> State (NodeState k) (Tree (Node k))
  buildNodeTree t@(T v ts) = do
    pNS@(MkNodeState p openR) <- get

    -- get info for current node
    let (openR', childrenAndRings) = computeNodeContext v p t openR
        ringChanges    = ringDelta openR openR'
        -- TODO adapt to upstream changes
        initialNOrd    = stereoBonds g v
        -- TODO adapt to upstream changes
        currentNOrd    = currentNeighbourOrdering v p childrenAndRings
        nodeLabel      = updateChirality initialNOrd currentNOrd (lab g v)

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


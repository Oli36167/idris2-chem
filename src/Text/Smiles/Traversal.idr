module Text.Smiles.Traversal

import Text.Molfile.Types

import Text.Smiles.Types
import Data.Tree
import Decidable.Equality

%default total
--------------------------------------------------------------------------------
--          helpers
--------------------------------------------------------------------------------

getChildrenFinK : {k : Nat} -> List (Tree (Fin k)) -> List (Fin k)
getChildrenFinK = map value

export
neighboursFor :
     (k : Nat)
  -> ChiralityData
  -> Maybe (List (ChiralNeighbour k))
neighboursFor k (MkCD k' ch ns) =
  case decEq k k' of
    Yes Refl => Just ns
    No _     => Nothing

bondSymbol : Bool -> SmilesBond -> String
bondSymbol bothArom bo =
  if bo == (if bothArom then Arom else Sngl)
     then ""
     else interpolate bo

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

allocateRingNr : {k :Nat} -> List (RingData k) -> RingNr
allocateRingNr ors =
   fromMaybe 0 $
     find (\x => not (elem x (map ringNr ors)))
          (mapMaybe refineRingNr [1..99])


parameters {k : Nat}
           (g : IGraph k SmilesBond SmilesAtom)

  public export
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
  public export
  initialNeighbourOrdering : Fin k -> List (ChiralNeighbour k)
  initialNeighbourOrdering v =
    case lab g v of
      SubsetAtom _ _ => []
      Bracket atom => fromMaybe [] (neighboursFor k atom.chirality)

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

  -- TODO make sure (with types) computeNodeContext uses the same funs
  -- (getChildrenFinK and ringNeighbours)
  public export
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
  public export
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


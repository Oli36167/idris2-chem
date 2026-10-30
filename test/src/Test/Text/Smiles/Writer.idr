module Test.Text.Smiles.Writer

import Chem

import Data.Graph.Indexed.Util as GU
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Query.Subgraph
import Data.String
import Data.Tree
import Data.Vect

import Derive.Prelude

import Hedgehog

import System.File

import Test.Data.Graph.Generators
import Test.Text.Smiles.Generators

import Text.Molfile.Types
import Text.ParseError
import Text.Smiles.Parser
import Text.Smiles.Types
import Text.Smiles.Writer

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Test data
--------------------------------------------------------------------------------

||| A short list of (smiles) strings, that is useful for testing and debugging
smilesTests : List String
smilesTests =
  [ "CC"
  , "[Cu+2].[O-]S(=O)(=O)[O-]"
  , "C1C(C2C(C3C(C4C(C5C(C6C(C7C(C8C(C9C(C%10C(CC)C%10C)C9C)C8C)C7C)C6C)C5C)C4C)C3C)C2C)C1"
  , "C12CC1C2"
  , "C[S@](=O)c1ccccc1"
  ]

covering
loadZinc : IO (List String)
loadZinc = do
  Right content <- readFile "../resources/zinc.txt"
    | Left err => do
        printLn err
        pure []

  pure (map trim (lines content))

genGraph : Gen (Graph SmilesBond SmilesAtom)
genGraph = lgraph (linear 1 50) (linear 0 80) bond atom

--------------------------------------------------------------------------------
--          Helpers
--------------------------------------------------------------------------------

export
smilesRoundtrip : String -> String
smilesRoundtrip s =
  case readSmiles' s of
    Left _        => "Parse error."
    Right (G _ g) => graphToSmiles g

||| Convenience function for manual testing. Might delete later.
smilesRoundtripIO : String -> IO ()
smilesRoundtripIO = putStrLn . smilesRoundtrip

||| Checks if converting a SMILES string into a graph yields an equivalent
||| graph as when converting to graph, then back to SMILES string
||| and then back to graph again.
covering
sameGraphAfterRoundtrip : String -> ChemRes [SmilesParseErr] Bool
sameGraphAfterRoundtrip s = do
  G o1 g1 <- readSmiles s
  G o2 g2 <- readSmiles (smilesRoundtrip s)
  pure $ isJust (query (==) (==) g1 g2)
                && (o1 == o2)
                && (GU.size g1 == GU.size g2)

-- Helpfull to to visualize a smiles graph (e.g. in the repl> :exec "CC(CO)C")
-- TODO replace with printTree from app/src/Prog/Trees.idr
printTree' : Interpolation n => IGraph k e n -> Tree (Fin k) -> IO ()
printTree' g = putStrLn . drawTree. map pretty
  where
    pretty : Fin k -> String
    pretty x = "\{show x}: \{lab g x}"

printSmilesIdxTree : String -> IO ()
printSmilesIdxTree s =
  case readSmiles' s of
       Left e        => putStrLn "An error occured"
       Right (G _ g) => traverse_ (printTree' g) $ dff' g

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

covering
testRoundtrips : List String -> Property
testRoundtrips ls = property1 $
  traverse_ (\(n, s) =>
    case sameGraphAfterRoundtrip s of
         Left _      => do
           footnote "failed to read Smiles: {s}"
           failure
         Right True  => success
         Right False => do
           footnote """
                    Line:      \{show n}
                    SMILES:    \{s}
                    Roundtrip: \{smilesRoundtrip s}
                    """
           failure
             ) (zip [1..(length ls)] ls)

covering
testRoundtripsMini : Property
testRoundtripsMini = testRoundtrips smilesTests

covering
testRoundtripsZincIO : IO Property
testRoundtripsZincIO = do
  zinc <- loadZinc
  pure (testRoundtrips zinc)

covering
testRoundtripsGen : Property
testRoundtripsGen = property $ do
  G _ g1 <- forAll genGraph
  let s = graphToSmiles g1
  case sameGraphAfterRoundtrip s of
    Left _      => do
                   footnote "failed to read Smiles: \{s}"
                   failure
    Right True  => success
    Right False => do
                   footnote "SMILES: \{s}"
                   failure

--------------------------------------------------------------------------------
--          parityTests
--------------------------------------------------------------------------------

-- TODO: Add public export to `anyFin` in Hedgehog.Internal.Gen
posFin : (n : Nat) -> (0 prf : IsSucc n) => Gen (Fin n)
posFin Z impossible
posFin (S k) = fin (linearFin k)

parameters (n          : Nat)
           {auto 0 prf : IsSucc n}

  genVect : Gen (Vect n Nat)
  genVect = pure (map finToNat (range {len = n}))

  genSwap : Gen (Fin n, Fin n)
  genSwap = MkPair <$> posFin n <*> posFin n

  genMultipleSwaps : (nSwaps : Nat) -> Gen (List (Fin n, Fin n))
  genMultipleSwaps nSwaps = Gen.list (linear nSwaps nSwaps) genSwap

swap : (i, j : Fin n) -> Vect n a -> Vect n a
swap i j v =
  case i == j of
    True => v
    _    => replaceAt j (index i v) $ replaceAt i (index j v) v

multipleSwaps : List (Fin n, Fin n) -> Vect n a -> Vect n a
multipleSwaps swaps v = foldl (\acc, (i, j) => swap i j acc) v swaps

countEffectiveSwaps : List (Fin n, Fin n) -> Nat
countEffectiveSwaps = count (\(i,j) => (i /= j))

parityTest : Ord a => List (Fin n, Fin n) -> Vect n a -> Bool
parityTest swaps v =
  let v' = multipleSwaps swaps v
      initial        = permutParity $ toList v
      final          = permutParity $ toList v'
      expectedChange = natToParity $ countEffectiveSwaps swaps
  in initial <+> expectedChange == final

parityTestGen : Property
parityTestGen = property $ do
  n      <- forAll $ Gen.nat $ linear 0 10
  v      <- forAll $ genVect (S n)
  nSwaps <- forAll $ Gen.nat $ linear 0 10
  swaps  <- forAll $ genMultipleSwaps (S n) nSwaps
  case parityTest swaps v of
    True  => success
    False => do
             footnote "Something went wrong"
             failure

--------------------------------------------------------------------------------
--          debugging
--------------------------------------------------------------------------------

covering
debugZincFirstFail : IO ()
debugZincFirstFail = do
  zinc <- loadZinc
  putStrLn "hello"
  let indexed = zip [1 .. length zinc] zinc
  for_ indexed $ \(n, s) => do
    case sameGraphAfterRoundtrip s of
      Right True => pure ()
      _ => do
        putStrLn "FAIL at line \{show n}"
        putStrLn s
        putStrLn "roundtrip: \{smilesRoundtrip s}"
        pure ()

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

covering
export
propsIO : IO Group
propsIO = do
  zincProp <- testRoundtripsZincIO
  pure $ MkGroup "Text.Smiles.Writer"
    [ ("testRoundtripsMini", testRoundtripsMini)
    , ("testRoundtripsZinc", zincProp)
    , ("testRoundtripsGen",  testRoundtripsGen)
    , ("parityTest",         parityTestGen)
    ]


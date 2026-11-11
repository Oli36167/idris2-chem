module Test.Text.Smiles.Stereo

import Test.Text.Smiles.Generators

%default total

Cast SmilesAtom HCount where
  cast (SubsetAtom elem arom) = 0
  cast (Bracket x) = cast x

readSG : String -> SmilesGraph
readSG = either (const $ G _ empty) id . readSmiles'

sizedGraph : (k : Nat) -> Graph e n -> Either Nat (IGraph k e n)
sizedGraph k (G f g) =
  case hdecEq k f of
    Just0 prf => Right $ rewrite prf in g
    Nothing0  => Left f

graphErr : String -> (exp,found : Nat) -> String
graphErr s x f =
  "Invalid graph order for \{s}. Expected \{show x} but found \{show f}."

testStereo : String -> (n : Nat) -> Fin n -> List (BStereo n) -> PropertyT ()
testStereo s n x exp =
  case sizedGraph n (readSG s) of
    Left f  => failWith Nothing (graphErr s n f)
    Right g => stereoBonds g x === exp

prop_stereo : Property
prop_stereo =
  property1 $ Prelude.do
    testStereo "N[C@](Br)(O)C" 5 1 [Bnd 0, Bnd 2, Bnd 3, Bnd 4]
    testStereo "[C@@](C)(Br)(O)N" 5 0 [Bnd 1, Bnd 2, Bnd 3, Bnd 4]
    testStereo "FC1C[C@](Br)(Cl)CCC1" 9 3 [Bnd 2, Bnd 4, Bnd 5, Bnd 6]
    testStereo "[C@]1(Br)(Cl)CCCC(F)C1" 9 0 [Bnd 8, Bnd 1, Bnd 2, Bnd 3]
    testStereo "N[C@H](O)C" 4 1 [Bnd 0, ImpH, Bnd 2, Bnd 3]
    testStereo "N1C2C3O[C@]123" 5 4 [Bnd 3, Bnd 0, Bnd 1, Bnd 2]
    testStereo "[C@]123OC1C2N3" 5 0 [Bnd 2, Bnd 3, Bnd 4, Bnd 1]
    testStereo "[C@H](N)(O)C" 4 0 [ImpH, Bnd 1, Bnd 2, Bnd 3]

export
props : Group
props =
  MkGroup "Text.Smiles.Stereo"
    [ ("prop_stereo", prop_stereo)
    ]

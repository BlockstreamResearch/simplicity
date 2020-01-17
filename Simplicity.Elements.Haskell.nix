{ mkDerivation, base, binary, cereal, lens-family, lib, MemoTrie, mtl, QuickCheck, stdenv, SHA, split, tasty, tasty-hunit, tasty-quickcheck, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity-Elements";
  version = "0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./. ["^LICENSE$" "^Simplicity-Elements\.cabal$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"])
    ["LICENSE" ".cabal" ".hs"];
  libraryHaskellDepends = [ base binary cereal lens-family MemoTrie mtl SHA split unification-fd vector ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  testTarget = ''--test-option="--quickcheck-replay=582534"'';

  license = stdenv.lib.licenses.mit;
})

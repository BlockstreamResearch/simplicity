{ mkDerivation, base, binary, cereal, lens-family, lib, MemoTrie, mtl, QuickCheck, stdenv, SHA, split, tasty, tasty-hunit, tasty-quickcheck, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity-Elements";
  version = "0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./. ["^LICENSE$" "^Simplicity-Elements\.cabal.delete-this-extension$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"])
    ["LICENSE" ".cabal.delete-this-extension" ".hs"];
  libraryHaskellDepends = [ base binary cereal lens-family MemoTrie mtl SHA split unification-fd vector ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  testTarget = ''--test-option="--quickcheck-replay=582534"'';

  prePatch = "mv ${pname}.cabal.delete-this-extension ${pname}.cabal";

  shellHook = "[ -f ${pname}.cabal.delete-this-extension ] && ln -sfT ${pname}.cabal.delete-this-extension Simplicity.cabal";

  license = stdenv.lib.licenses.mit;
})

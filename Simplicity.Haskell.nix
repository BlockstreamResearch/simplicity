{ mkDerivation, base, lens-family, lib, QuickCheck, stdenv, tasty, tasty-hunit, tasty-quickcheck, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity";
  version = "0.0.0";
  src = lib.sourceByRegex ./. ["^Simplicity\.cabal$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"];
  libraryHaskellDepends = [ base lens-family unification-fd vector ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  license = stdenv.lib.licenses.unfree;
})

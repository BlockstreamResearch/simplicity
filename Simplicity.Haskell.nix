{ mkDerivation, base, binary, cereal, lens-family, lib, MemoTrie, mtl, prettyprinter, QuickCheck, stdenv, split, tasty, tasty-hunit, tasty-quickcheck, tardis, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity";
  version = "0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./. ["^LICENSE$" "^Simplicity\.cabal$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"
                              "^Haskell-Generate$" "^Haskell-Generate/.*"
                              "^C$" "^C/.*"])
    ["LICENSE" ".cabal" ".hs" ".hsig" ".h" ".c" ".inc"];
  libraryHaskellDepends = [ base binary cereal lens-family MemoTrie mtl split tardis unification-fd vector ];
  executableHaskellDepends = [ prettyprinter ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  enableParallelBuilding = true;
  preCheck = ''
    export GHCRTS=-N$NIX_BUILD_CORES
  '';
  postCheck = ''
    unset GHCRTS
  '';
  # Uncomment to make testing deterministic.
  # testFlags = ["--quickcheck-replay=582534"];

  # Cabal's haddock doesn't work for Backpack / internal libraries / modules reexports.
  # Until that is fix we manually generate some documentation pages
  haddockFlags = ["--haddock-option='--use-contents=index.html'"];
  postHaddock = ''
    cp ${./manual-index.html} dist/doc/html/Simplicity/index.html
    cp ${./Simplicity-Primitive.html} dist/doc/html/Simplicity/Simplicity-Primitive.html
  '';

  license = lib.licenses.mit;
})

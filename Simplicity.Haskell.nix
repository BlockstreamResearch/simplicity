{ mkDerivation, cabal-install, base, binary, cereal, lens-family, lib, MemoTrie, mtl, QuickCheck, stdenv, split, tasty, tasty-hunit, tasty-quickcheck, tardis, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity";
  version = "0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./. ["^LICENSE$" "^Simplicity\.cabal$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"
                              "^Haskell-GenerateC$" "^Haskell-GenerateC/.*"
                              "^C$" "^C/uword.h" "^C/bitstring.h" "^C/frame.*" "^C/jets.*" "^C/sha256.*" "^C/unreachable.h"
                              "^C/ascii.h" "^C/prefix.h" "^C/tag.h"
                              "^C/jets-secp256k1.c$" "^C/secp256k1$" "^C/secp256k1/.*"
                              "^C/include$" "^C/include/simplicity$" "^C/include/simplicity/elements$" "^C/include/simplicity/elements/env.h"
                              "^C/primitive$" "^C/primitive/elements$" "^C/primitive/elements/jets.*" "^C/primitive/elements/ops.*" "^C/primitive/elements/primitive.*" "^C/primitive/elements/env.c"])
    ["LICENSE" ".cabal" ".hs" ".hsig" ".h" ".c"];
  libraryHaskellDepends = [ base binary cereal lens-family MemoTrie mtl split tardis unification-fd vector ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  preCheck = ''
    export GHCRTS=-N$NIX_BUILD_CORES
  '';
  postCheck = ''
    unset GHCRTS
  '';
  # Uncomment to make testing deterministic.
  # testFlags = ["--quickcheck-replay=582534"];

  # Cabal's haddock doesn't work for Backpack / internal libraries / modules reexports.
  # Under ghc8, the documenation generated is pretty badly broken.
  # Under ghc9, Setup.hs haddock simply crashes.
  #
  # To work around these issues we manually build the documentation using cabal haddock.
  # Even cabal haddock hardcodes links to internal modules that are reexported which is a problem.
  # To deal with that, we build directly into the $doc directly.
  # This isn't very great because the documenation isn't really in the right place, but the result is usable.
  doHaddock = false;
  enableSeparateDocOutput = true;
  buildTools = [ cabal-install ];
  postHaddock = ''
   CABAL_CONFIG=/dev/null CABAL_DIR=`pwd` env -u GHC_PACKAGE_PATH cabal --package-db=$packageConfDir configure --docdir=$doc/share/doc/${pname}-${version}
   CABAL_CONFIG=/dev/null CABAL_DIR=`pwd` env -u GHC_PACKAGE_PATH cabal --package-db=$packageConfDir haddock --distdir=$doc
  '';
  # Delete all cabal build material other than the documentation.
  postInstall = ''
    find $doc ! -path '*/doc/*' -delete ||:
  '';

  license = lib.licenses.mit;
})

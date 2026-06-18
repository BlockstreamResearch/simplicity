{ lib, stdenv, cmake }:
stdenv.mkDerivation {
  name = "libBitcoinSimplicity-cmake";
  src = lib.sourceFilesBySuffices ./C ["CMakeLists.txt" ".c" ".h" ".inc"];
  nativeBuildInputs = [ cmake ];
  # Release/RelWithDebInfo/MinSizeRel all define NDEBUG, which simplicity_assert.h rejects
  # unless RECKLESS is also defined.
  cmakeBuildType = "Debug";
  doCheck = false;
  # CMakeLists.txt has no install() rules yet; stash the built static library
  # as the output so this remains a meaningful smoke test.
  installPhase = ''
    mkdir -p $out/lib
    cp libBitcoinSimplicity.a $out/lib/
  '';
  meta = {
    license = lib.licenses.mit;
  };
}

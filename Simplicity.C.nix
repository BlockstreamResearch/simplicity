{ lib, stdenv, gcovr ? null, wideMultiply ? null, withCoverage ? false
, production ? false
, gcov-executable ? if stdenv.cc.isGNU then "gcov" else
                    if stdenv.cc.isClang then "${stdenv.cc.cc.libllvm}/bin/llvm-cov gcov"
                    else null
, doCheck ? true
}:
assert wideMultiply == null
    || wideMultiply == "int64"
    || wideMultiply == "int128"
    || wideMultiply == "int128_struct";
assert withCoverage -> gcovr != null && gcov-executable != null;
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h" ".inc"];
  enableParallelBuilding = true;
  CPPFLAGS = lib.optional (builtins.isString wideMultiply) "-DUSE_FORCE_WIDEMUL_${lib.toUpper wideMultiply}=1";
  CFLAGS = lib.optional withCoverage "--coverage"
        ++ lib.optional production "-DPRODUCTION";
  LDFLAGS = lib.optional withCoverage "--coverage";
  inherit doCheck;
  postCheck = lib.optional withCoverage ''
    mkdir -p $out/shared/coverage
    ${gcovr}/bin/gcovr --gcov-executable "${gcov-executable}" --verbose --html --html-details -o $out/shared/coverage/coverage.html
  '';
  meta = {
    license = lib.licenses.mit;
  };
}

{ lib, stdenv, gcovr ? null, wideMultiply ? null, withCoverage ? false
, withProfiler ? false, gperftools ? null, graphviz ? null, perl ? null, librsvg ? null
, withTiming ? true
, withValgrind ? false, valgrind ? null
, production ? false
, enableShaNI ? stdenv.hostPlatform.isx86_64
, gcov-executable ? if stdenv.cc.isGNU then "gcov -r" else
                    if stdenv.cc.isClang then "${stdenv.cc.cc.libllvm}/bin/llvm-cov gcov"
                    else null
, doCheck ? true
}:
assert wideMultiply == null
    || wideMultiply == "int64"
    || wideMultiply == "int128"
    || wideMultiply == "int128_struct";
assert withCoverage -> gcovr != null && gcov-executable != null;
assert withProfiler -> gperftools != null && graphviz != null && perl != null && librsvg != null;
assert withValgrind -> valgrind != null;
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h" ".inc"];
  enableParallelBuilding = true;
  CPPFLAGS = lib.optional (builtins.isString wideMultiply) "-DUSE_FORCE_WIDEMUL_${lib.toUpper wideMultiply}=1";
  CFLAGS = lib.optional withCoverage "--coverage"
        ++ lib.optional withTiming "-DTIMING_FLAG"
        ++ lib.optional production "-DPRODUCTION";
  LDFLAGS = lib.optional withCoverage "--coverage"
         ++ lib.optional withProfiler "-lprofiler";
  preBuild = lib.optional (enableShaNI) ''
     makeFlagsArray+=(X86_SHANI_CXXFLAGS="-msse4.1 -msha")
  '';
  inherit doCheck;
  checkInputs = lib.optionals withProfiler [ gperftools ];
  nativeCheckInputs = lib.optionals withProfiler [ graphviz ]
                   ++ lib.optionals withValgrind [ valgrind ];
  postCheck = lib.optional withCoverage ''
    mkdir -p $out/shared/coverage
    ${gcovr}/bin/gcovr --gcov-executable "${gcov-executable}" --verbose --html --html-details -o $out/shared/coverage/coverage.html
  '' ++ lib.optional withProfiler ''
    mkdir -p $out/shared/profile
    CPUPROFILE=./prof.out CPUPROFILE_FREQUENCY=1000 ./test
    # Until https://github.com/NixOS/nixpkgs/pull/279623 is resolved, we need to explicitly invoke perl
    ${perl}/bin/perl ${gperftools}/bin/pprof --svg ./test prof.out > $out/shared/profile/test.svg
    ${librsvg}/bin/rsvg-convert -f pdf -o $out/shared/profile/test.pdf $out/shared/profile/test.svg
  '' ++ lib.optional withValgrind ''
    valgrind  --leak-check=full --error-exitcode=1 ./test --no-timing
  '';
  meta = {
    license = lib.licenses.mit;
  };
}

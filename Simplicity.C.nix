{ lib, stdenv, wideMultiply ? null }:
assert wideMultiply == null
    || wideMultiply == "int64"
    || wideMultiply == "int128"
    || wideMultiply == "int128_struct";
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h" ".inc"];
  CPPFLAGS = lib.optional (builtins.isString wideMultiply) "-DUSE_FORCE_WIDEMUL_${lib.toUpper wideMultiply}=1";
  doCheck = true;
  meta = {
    license = lib.licenses.mit;
  };
}

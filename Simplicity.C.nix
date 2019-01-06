{ lib, stdenv, libsha256compression }:
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h"];
  buildInputs = [ libsha256compression ];
  doCheck = true;
  meta = {
    license = lib.licenses.mit;
  };
}

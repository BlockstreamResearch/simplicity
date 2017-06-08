{ mkDerivation, base, stdenv, unification-fd }:
mkDerivation {
  pname = "Simplicity";
  version = "0.0.0";
  src = ./.;
  libraryHaskellDepends = [ base unification-fd ];
  license = stdenv.lib.licenses.unfree;
}

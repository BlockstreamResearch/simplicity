{ coq, lib, stdenv }:
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  src = lib.sourceByRegex ./Coq ["Simplicity" ".*v$"];
  postConfigure = ''
    coq_makefile -Q Simplicity Simplicity **/*.v > Makefile
  '';
  buildInputs = [ coq ];
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.unfree;
  };
}

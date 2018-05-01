{ coq, lib, vst, stdenv }:
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    [".v"];
  postConfigure = ''
    shopt -s globstar
    coq_makefile -Q Simplicity Simplicity -Q Util Util **/*.v > Makefile
  '';
  buildInputs = [ coq ];
  propagatedBuildInputs = [ vst ];
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.unfree;
  };
}

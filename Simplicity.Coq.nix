{ alectryon, coq, serapi, lib, vst, stdenv }:
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["_CoqProject" "C" "C/.*" "Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    ["_CoqProject" ".v"];
  outputs = [ "out" "doc" ];
  postConfigure = ''
    coq_makefile -f _CoqProject -o CoqMakefile
  '';
  buildInputs = [ coq serapi alectryon ];
  propagatedBuildInputs = [ vst ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  postInstall = ''
    alectryon --frontend coq --output-directory $doc --webpage-style windowed -R C C C/secp256k1/verif_int128_impl.v
  '';
  meta = {
    license = lib.licenses.mit;
  };
}

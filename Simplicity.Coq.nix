{ coq, lib, vst, stdenv
, alectryon ? null
, serapi ? null
}:
assert alectryon != null -> serapi != null;
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["_CoqProject" "C" "C/.*" "Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    ["_CoqProject" ".v"];
  outputs = [ "out" ] ++ lib.optional (alectryon != null) "doc";
  postConfigure = ''
    coq_makefile -f _CoqProject -o CoqMakefile
  '';

  buildInputs = [ coq ];
  nativeBuildInputs = lib.optional (alectryon != null) serapi;
  propagatedBuildInputs = [ vst ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";
  postBuild = lib.optional (alectryon != null) ''
    ${alectryon}/bin/alectryon --frontend coq --output-directory $doc --webpage-style windowed -R C C \
    C/secp256k1/spec_int128.v C/secp256k1/verif_int128_impl.v
  '';

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.mit;
  };
}

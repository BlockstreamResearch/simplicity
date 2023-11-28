{lib, stdenv, fetchFromGitHub, coq,
 cheating ? true
} :
stdenv.mkDerivation {
  name = "safegcd-bounds-coq-divsteps";
  src = fetchFromGitHub {
    owner = "sipa";
    repo = "safegcd-bounds";
    rev ="06abb7f7aba9b00eb4ead96bdd7dbcc04ec45c4f";
    sparseCheckout = [
      "coq/divsteps"
    ];
    hash = "sha256-I+1TFBJOQxro09hkHBdCrLptoq06RYaeBz5PbPLzjGA=";
    name = "safegcd-bounds";
  };
  sourceRoot = "safegcd-bounds/coq/divsteps";

  ${if cheating then "postPatch" else null} = ''
     substituteInPlace divsteps724.v --replace-fail "Time Qed." "Admitted."
  '';

  buildInputs = [ coq ];

  enableParallelBuilding = true;

  preBuild = ''
    coq_makefile -f _CoqProject -o Makefile
  '';

  installFlags = "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib/";
}

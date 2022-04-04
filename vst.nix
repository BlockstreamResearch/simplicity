{stdenv, fetchFromGitHub, coq, compcert } :
stdenv.mkDerivation {
  name = "vst-sha256-2.9.1";
  src = fetchFromGitHub {
    owner = "PrincetonUniversity";
    repo = "VST";
    rev ="v2.9.1";
    hash = "sha256-q/Us8bG1Sek2cuAT6mvwxihBKrVl77RW9m0N5uWOQL4=";
  };

  buildInputs = [ coq ];
  propagatedBuildInputs = [ compcert ];

  patches = [ ];

  postPatch = ''
    substituteInPlace util/coqflags \
      --replace "/usr/bin/env bash" ${stdenv.shell} \
      --replace "\`/bin/pwd\`" "$out/lib/coq/${coq.coq-version}/user-contrib/VST"
    substituteInPlace util/calc_install_files \
      --replace "/usr/bin/env bash" ${stdenv.shell} \
  '';

  enableParallelBuilding = true;

  makeFlags = [ "COMPCERT=inst_dir" "COMPCERT_INST_DIR=${compcert}/lib/coq/${coq.coq-version}/user-contrib/compcert" "INSTALLDIR=$(out)/lib/coq/${coq.coq-version}/user-contrib/VST" ];

  buildFlags = [ "default_target" "sha" ];

  postBuild = ''
    gcc -c sha/sha.c -o sha/sha.o
  '';

  postInstall = ''
    install -d "$out/lib/coq/${coq.coq-version}/user-contrib/sha"
    find sha -name \*.vo -exec sh -c '
     install -m 0644 -T "$0" "$out/lib/coq/${coq.coq-version}/user-contrib/$0"
     install -m 0644 -T "''${0%.vo}.v" "$out/lib/coq/${coq.coq-version}/user-contrib/''${0%.vo}.v"
    ' {} \;
    install -d "$out/lib/sha"
    install -m 0644 -t "$out/lib/sha" "sha/sha.o" "sha/sha.h"
    install -d "$out/share"
    install -m 0644 -t "$out/share" "_CoqProject-export"
  '';
}

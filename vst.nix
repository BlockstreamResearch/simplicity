{lib, stdenv, fetchFromGitHub, coq, compcert,
 ignoreCompcertVersion ? compcert.version=="3.13.1" # Temporarily allow compcert 3.13
} :
stdenv.mkDerivation {
  name = "vst-sha256-2.12";
  src = fetchFromGitHub {
    owner = "PrincetonUniversity";
    repo = "VST";
    rev ="v2.12";
    hash = "sha256-4HL0U4HA5/usKNXC0Dis1UZY/Hb/LRd2IGOrqrvdWkw=";
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

  makeFlags =
    lib.optional ignoreCompcertVersion "IGNORECOMPCERTVERSION=true" ++
  [
    "COMPCERT=inst_dir"
    "COMPCERT_INST_DIR=${compcert}/lib/coq/${coq.coq-version}/user-contrib/compcert"
    "INSTALLDIR=$(out)/lib/coq/${coq.coq-version}/user-contrib/VST"
  ];

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

{stdenv, fetchurl, coq, compcert } :
stdenv.mkDerivation {
  name = "vst-sha256-2.6";
  src = fetchurl {
    url = "https://github.com/PrincetonUniversity/VST/archive/v2.6.tar.gz";
    sha256 = "1x5jarch8pbrld1s6r1yk49y17m9v2jkwl8gfa4sn4szcl4zvq6p";
  };

  buildInputs = [ coq ];
  propagatedBuildInputs = [ compcert ];

  patches = [ ./vst-version.patch ./vst-makefile.patch ];
  postPatch = ''
    substituteInPlace util/coqflags \
      --replace "/usr/bin/env bash" ${stdenv.shell} \
      --replace "\`/bin/pwd\`" "$out/lib/coq/${coq.coq-version}/user-contrib/VST"
    substituteInPlace util/calc_install_files \
      --replace "/bin/bash" ${stdenv.shell}
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

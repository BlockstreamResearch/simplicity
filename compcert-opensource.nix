{ stdenv, lib, fetchurl
, coq, flocq, ocaml, menhir, findlib
, ccomp-platform ? if stdenv.isDarwin then "x86_64-macosx" else "x86_64-linux"
}:

assert lib.versionAtLeast ocaml.version "4.05";
assert lib.versionAtLeast coq.coq-version "8.7";

stdenv.mkDerivation {
  pname = "compcert";
  version = "3.7";

  src = fetchurl {
    url = "https://github.com/AbsInt/CompCert/archive/v3.7.tar.gz";
    sha256 = "1c3yp3ns830vg3q8b0y61xffd1fgkmkg585pdsv6qmy2sqp1pvnf";
  };

  # Unpack only those files that are open source licensed (GPL2 or GPL3).
  unpackPhase = ''
    tar -xf $src --wildcards --no-wildcards-match-slash \
      'CompCert*/MenhirLib' \
      'CompCert*/lib' \
      'CompCert*/common' \
      'CompCert*/cfrontend/C2C.ml' \
      'CompCert*/cfrontend/Clight.v' \
      'CompCert*/cfrontend/ClightBigstep.v' \
      'CompCert*/cfrontend/Cop.v' \
      'CompCert*/cfrontend/CPragmas.ml' \
      'CompCert*/cfrontend/Csem.v' \
      'CompCert*/cfrontend/Cstrategy.v' \
      'CompCert*/cfrontend/Csyntax.v' \
      'CompCert*/cfrontend/Ctypes.v' \
      'CompCert*/cfrontend/Ctyping.v' \
      'CompCert*/cfrontend/PrintClight.ml' \
      'CompCert*/cfrontend/PrintCsyntax.ml' \
      'CompCert*/backend/Cminor.v' \
      'CompCert*/backend/PrintCminor.ml' \
      'CompCert*/cparser' \
      'CompCert*/exportclight' \
      'CompCert*/*/Archi.v' \
      'CompCert*/*/Builtins1.v' \
      'CompCert*/*/CBuiltins.ml' \
      'CompCert*/*/extractionMachdep.v' \
      'CompCert*/extraction/extraction.v' \
      'CompCert*/configure' \
      'CompCert*/Makefile' \
      'CompCert*/Makefile.extr' \
      'CompCert*/Makefile.menhir' \
      'CompCert*/LICENSE' \
      'CompCert*/README.md' \
      'CompCert*/VERSION'
    cd CompCert*
    mkdir doc
  '';

  patches = [ (fetchurl {
                url="https://raw.githubusercontent.com/coq/opam-coq-archive/ac224efae1204e12313897df67c1d40ff2649571/released/packages/coq-compcert/coq-compcert.3.7%7Ecoq-platform%7Eopen-source/files/0007-Dual-license-aarch64-Archi.v-Cbuiltins.ml-extraction.patch";
                sha256="1mwl61wjbkj53mn1y9rx324vhvn6lng47y9xylh4yzh9ni2g8rpx";
              })
              (fetchurl {
                url="https://raw.githubusercontent.com/coq/opam-coq-archive/ac224efae1204e12313897df67c1d40ff2649571/released/packages/coq-compcert/coq-compcert.3.7%7Ecoq-platform%7Eopen-source/files/0008-Update-the-list-of-dual-licensed-files.patch";
                sha256="0zfvvqmv8lnay76gwv7ydwbhl02401qcavmylh11vcwy1qgj8va0";
              })
              (fetchurl {
                url="https://raw.githubusercontent.com/coq/opam-coq-archive/ac224efae1204e12313897df67c1d40ff2649571/released/packages/coq-compcert/coq-compcert.3.7%7Ecoq-platform%7Eopen-source/files/0011-Use-Coq-platform-supplied-Flocq.patch";
                sha256="1w6z1z2r21kfm29x9hjmbidzvm4kzilcq2l11gind99w108kxm8z";
              })
              ./compcert-opensource.patch ];

  buildInputs = [ ocaml findlib coq menhir ];
  propagatedBuildInputs = [ flocq ];

  enableParallelBuilding = true;

  configurePhase = ''
    ./configure \
      -bindir $out/bin \
      -libdir $out/lib \
      -install-coqdev \
      -coqdevdir $out/lib/coq/${coq.coq-version}/user-contrib/compcert \
      -ignore-coq-version \
      ${ccomp-platform}
  '';

  preBuild = "make depend";
  buildFlags = [ "proof" "exportclight/Clightdefs.vo" ];

  meta = with lib; {
    description = "Formally verified C compiler";
    homepage    = "http://compcert.inria.fr";
    license     = licenses.gpl3; # These particular files are all gpl3 compatible.
    platforms   = [ "x86_64-linux" "x86_64-darwin" ];
  };
}

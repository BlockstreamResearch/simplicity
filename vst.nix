{stdenv, fetchurl, coq} :
stdenv.mkDerivation {
  name = "vst-sha256-2.0";
  src = fetchurl {
    url = "https://github.com/PrincetonUniversity/VST/archive/v2.0.tar.gz";
    sha256 = "0kbb29xj5n4sj7i3n7x05zcj9yswnc4kxy4hqx8m8wrmz9cxql8p";
  };

  buildInputs = [ coq ];


  buildPhase = ''
    IGNORECOQVERSION=true make sha/functional_prog.vo
    gcc -c sha/sha.c -o sha/sha.o
  '';
  installPhase = ''
    find . -name \*.vo -exec sh -c '
     mkdir -p "$out/lib/coq/${coq.coq-version}/user-contrib/VST/''${0%/*}"
     mv "$0" "$out/lib/coq/${coq.coq-version}/user-contrib/VST/$0"
     mv "''${0%.vo}.v" "$out/lib/coq/${coq.coq-version}/user-contrib/VST/''${0%.vo}.v"
     mv "''${0%.vo}.glob" "$out/lib/coq/${coq.coq-version}/user-contrib/VST/''${0%.vo}.glob"
    ' {} \;
    mv $out/lib/coq/${coq.coq-version}/user-contrib/VST/compcert $out/lib/coq/${coq.coq-version}/user-contrib/compcert
    mv $out/lib/coq/${coq.coq-version}/user-contrib/VST/sha $out/lib/coq/${coq.coq-version}/user-contrib/sha
    mkdir -p $out/lib/sha
    cp sha/sha.o $out/lib/sha/
    cp sha/sha.h $out/lib/sha/
  '';
}

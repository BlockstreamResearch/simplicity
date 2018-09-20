{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "c23664e0d51c4f2e1dbf554a9ed4031026bcf07b"; # simplicity branch
    sha256 = "1flpx965l36pd3c4yxp9p3xkw97r2qwkz0gcfp2mn40911qaff5v";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}

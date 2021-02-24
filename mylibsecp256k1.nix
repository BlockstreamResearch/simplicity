{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "f97247cf5527ad2d52574c13d3fe6b61f4b20011"; # simplicity branch
    sha256 = "0xwsda3yi9dym9faj5wpzjdhpqy2vavsfszszm7gbwlixx88wmxq";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/scalar_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}

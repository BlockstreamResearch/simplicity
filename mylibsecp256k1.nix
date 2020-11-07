{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "f659876dda3eec85fc66ce3972b797d97627ce1d"; # simplicity branch
    sha256 = "1qglvj1qkpjilxzl0rhy7lvhkwbfdgs859fcb2mms3gk7lqrh24x";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/scalar_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}

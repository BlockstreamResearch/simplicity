{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "7f59f10d224334a0582a8de1dbd4edb70a6d6b94"; # simplicity branch
    sha256 = "0cgxyv4fp57knjqg57yqs88vnj97qzvv6kn3pqsxwabprqw21v6w";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}

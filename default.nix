{ nixpkgs ? import <nixpkgs> {}
, ghc ? "ghc94"
, coqPackages ? "coqPackages_8_15"
, secp256k1git ? null
, wideMultiply ? null
, env ? "stdenv"
}:
let hp = nixpkgs.haskell.packages.${ghc};
    cp = nixpkgs.${coqPackages};
 in rec
{
  haskell = haskellPackages.callPackage ./Simplicity.Haskell.nix {};

  haskellPackages = hp.override {
    overrides = self: super: {
      Simplicity = haskell;

      # Temporary work around for compiling hlint and hasktags in ghc94.
      microlens = self.microlens_0_4_13_1;
      microlens-ghc = self.microlens-ghc_0_4_14_1;
      microlens-platform = self.microlens-platform_0_4_3_3;
      hlint = self.hlint_3_5;
    };
  };

  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    inherit (cp) coq;
    inherit vst;
  };

  c = nixpkgs.callPackage ./Simplicity.C.nix {
    inherit wideMultiply;
    stdenv = nixpkgs.${env};
  };

  compcert = nixpkgs.callPackage ./compcert-opensource.nix {
    inherit (cp) coq flocq;
    inherit (cp.coq.ocamlPackages) ocaml menhir menhirLib findlib;
    ccomp-platform = "x86_64-linux";
  };

  vst = nixpkgs.callPackage ./vst.nix {
    inherit (cp) coq;
    inherit compcert;
  };

  # $ nix-build -A inheritance -o inheritance.Coq.eps
  inheritance = nixpkgs.runCommand "inheritance.Coq.eps" { buildInputs = [ nixpkgs.graphviz ]; } "dot ${./inheritance.Coq.dot} -Teps -o $out";

  # build the object file needed by Haskell's Simplicity.LibSecp256k1.FFI module
  # e.g. $ nix-build --arg secp256k1git ~/secp256k1 -A mylibsecp256k1 -o libsecp256k1.o
  mylibsecp256k1 = nixpkgs.callPackage ./mylibsecp256k1.nix {
    inherit secp256k1git;
  };
}

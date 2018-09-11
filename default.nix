{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822", coqVersion ? "coq", secp256k1git ? null}: rec
{
  haskell = nixpkgs.haskell.packages.${compiler}.callPackage ./Simplicity.Haskell.nix { };
  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    inherit vst;
    coq = nixpkgs.${coqVersion};
  };
  vst = nixpkgs.callPackage ./vst.nix {
    coq = nixpkgs.${coqVersion};
  };

  # $ nix-build -A inheritance -o inheritance.Coq.eps
  inheritance = nixpkgs.runCommand "inheritance.Coq.eps" { buildInputs = [ nixpkgs.graphviz ]; } "dot ${./inheritance.Coq.dot} -Teps -o $out";

  # build the object file needed by Haskell's Simplicity.LibSecp256k1.FFI module
  # e.g. $ nix-build --arg secp256k1git ~/secp256k1 -A mylibsecp256k1 -o libsecp256k1.o
  mylibsecp256k1 = nixpkgs.callPackage ./mylibsecp256k1.nix {
    inherit secp256k1git;
  };
}

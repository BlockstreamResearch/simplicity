{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822", coqVersion ? "coq" }: rec
{
  haskell = nixpkgs.haskell.packages.${compiler}.callPackage ./Simplicity.Haskell.nix { };
  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    inherit vst;
    coq = nixpkgs.${coqVersion};
  };
  vst = nixpkgs.callPackage ./vst.nix {
    coq = nixpkgs.${coqVersion};
  };

  # nix-build -A inheritance -o inheritance.Coq.eps
  inheritance = nixpkgs.runCommand "inheritance.Coq.eps" { buildInputs = [ nixpkgs.graphviz ]; } "dot ${./inheritance.Coq.dot} -Teps -o $out";
}

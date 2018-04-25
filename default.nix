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
}

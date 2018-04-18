{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822" }: rec
{
  haskell = nixpkgs.haskell.packages.${compiler}.callPackage ./Simplicity.Haskell.nix { };
  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    inherit vst;
  };
  vst = nixpkgs.callPackage ./vst.nix { };
}

{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc822" }:
{
  haskell = nixpkgs.haskell.packages.${compiler}.callPackage ./Simplicity.Haskell.nix { };
  coq = nixpkgs.callPackage ./Simplicity.Coq.nix { };
}

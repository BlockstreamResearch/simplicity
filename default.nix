{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc802" }:
nixpkgs.haskell.packages.${compiler}.callPackage ./Simplicity.Haskell.nix { }

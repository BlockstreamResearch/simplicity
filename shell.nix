{ haskell ? true
, coq     ? true
, c       ? true
, nixpkgs ? import <nixpkgs> {}
}:
let
  simplicity      = import ./. {};
  optional        = nixpkgs.lib.optional;
  haskellDevTools = pkgs: with pkgs; [cabal-install hlint hasktags];
  haskellPkgs     = pkgs: simplicity.haskell.buildInputs ++ haskellDevTools pkgs;
  haskellDevEnv   = simplicity.haskellPackages.ghcWithPackages haskellPkgs;

  selectedPkgs = optional false false # haskell simplicity.haskell # haskellDrv
              ++ optional coq     simplicity.coq
              ++ optional c       simplicity.c;
in
  nixpkgs.mkShell {
    packages = optional haskell haskellDevEnv;
    inputsFrom = optional coq     simplicity.coq
              ++ optional c       simplicity.c;
  }

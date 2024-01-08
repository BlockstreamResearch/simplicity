{ haskell ? true
, coq     ? true
, c       ? true
, nixpkgs ? import <nixpkgs> {}
, ghc ? "ghc94"
, coqPackages ? "coqPackages_8_16"
, env ? "stdenv"
, withCoverage ? true
, withProfiler ? true
}:
let
  simplicity      = import ./. {inherit nixpkgs ghc coqPackages env withCoverage withProfiler;};
  optional        = nixpkgs.lib.optional;
  haskellDevTools = pkgs: with pkgs; [cabal-install hlint hasktags];
  haskellPkgs     = pkgs: simplicity.haskell.buildInputs ++ simplicity.haskell.propagatedBuildInputs ++ haskellDevTools pkgs;
  haskellDevEnv   = simplicity.haskellPackages.ghcWithPackages haskellPkgs;
  coqDevEnv       = [ nixpkgs.python3Packages.alectryon
                      nixpkgs.${coqPackages}.serapi
                      nixpkgs.${coqPackages}.coq
                      nixpkgs.${coqPackages}.coqide
                    ];

in
  nixpkgs.mkShell {
    packages = optional haskell haskellDevEnv
            ++ optional coq coqDevEnv;
    inputsFrom = optional coq     simplicity.coq
              ++ optional c       simplicity.c;
  }

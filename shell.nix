{ haskell ? true
, coq     ? true
, c       ? true
, nixpkgs ? import <nixpkgs> {}
}:
let
  simplicity      = import ./. {};
  optional        = nixpkgs.lib.optional;
  mkDerivation    = nixpkgs.stdenv.mkDerivation;

  haskellDrv =
    let
      haskellDevTools = pkgs: with pkgs; [cabal-install hlint hasktags];
      haskellPkgs     = pkgs: simplicity.haskell.buildInputs ++ haskellDevTools pkgs;
      haskellDevEnv   = simplicity.haskellPackages.ghcWithPackages haskellPkgs;
    in
      mkDerivation {
        name = "haskell-dev-env";
        buildInputs = [haskellDevEnv];
      };

  mergePkgs = name: drvs: mkDerivation {
    inherit name;
    buildInputs           = builtins.concatMap (p: p.buildInputs) drvs;
    nativeBuildInputs     = builtins.concatMap (p: p.nativeBuildInputs) drvs;
    propagatedBuildInputs = builtins.concatMap (p: p.propagatedBuildInputs) drvs;
  };

  selectedPkgs = optional haskell haskellDrv
              ++ optional coq     simplicity.coq
              ++ optional c       simplicity.c;
in
  mergePkgs "simplicity-dev-env" selectedPkgs

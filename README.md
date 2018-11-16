# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Documentation

Detailed documentation can be found in the `Simplicity.tm` TeXmacs file.

## Build

Software artifacts can be built using [Nix](https://nixos.org/nix/).
To build the Haskell project, run `nix-build -A haskell`.
To build the Coq project, run `nix-build -A coq`.

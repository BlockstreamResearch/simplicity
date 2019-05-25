# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Build

Software artifacts can be built using [Nix](https://nixos.org/nix/).

* To build the Haskell project, run `nix-build -A haskell`.
* To use the Haskell project, try `nix-shell -p "(import ./default.nix {}).haskellPackages.ghcWithPackages (pkgs: [pkgs.Simplicity])"`.
* To build the Coq project, run `nix-build -A coq`.

## Documentation

Detailed documentation can be found in the `Simplicity-TR.tm` TeXmacs file.
A recent PDF version can be found in the [pdf](https://github.com/ElementsProject/simplicity/blob/pdf/Simplicity-TR.pdf) branch.

## Further Resources

* Our [paper that originally introduced Simplicity](https://arxiv.org/abs/1711.03028).  Some of the finer details are out of date, but it is still a good introduction.
* [BPASE 2018 presentation](https://youtu.be/VOeUq3oR2fk) of the above paper ([slides](https://cyber.stanford.edu/sites/g/files/sbiybj9936/f/slides-bpase-2018.pdf)).
* [Scale by the Bay 2018 presentation](https://youtu.be/M4XnDrRIKx8) that illustrates formal verification of Simplicity in Agda ([slides](https://lists.ozlabs.org/pipermail/simplicity/2018/000011.html)).

## Contact

Interested parties are welcome to join the [Simplicity mailing list](https://lists.ozlabs.org/listinfo/simplicity).
Issues and pull-requests can be made through GitHub's interface.

# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Build

Software artifacts can be built using [Nix](https://nixos.org/nix/).
To build the Haskell project, run `nix-build -A haskell`.
To build the Coq project, run `nix-build -A coq`.

To build the Coq part without Nix, you can try:

1. download and extract VST from the URL in `vst.nix`
1. in the VST directory, do: `make compcert/lib/Integers.vo sha/SHA256.vo sha/functional_prog.vo`
1. in the root Simplicity directory, do:
1. `dune build Coq/Util`
1. `dune build Coq/Simplicity`
1. Proof General won't find the built `vo` files unless they are moved from the directory where Dune puts them: `for i in $(find _build/default/Coq -name '*.vo' ); do mv -v $i $(echo $i | cut -d/ -f3-); done`
1. Now you can use Proof General to browse the proofs.

## Documentation

Detailed documentation can be found in the `Simplicity-TR.tm` TeXmacs file.
A recent PDF version can be found in the [pdf](https://github.com/ElementsProject/simplicity/blob/pdf/Simplicity-TR.pdf) branch.

## Further Resources

* Our [paper that originally introduced Simplicity](https://arxiv.org/abs/1711.03028).  Some of the finer details are out of date, but it is still a good introduction.
* [BPASE 2018 presentation](https://youtu.be/VOeUq3oR2fk) of the above paper ([slides](https://cyber.stanford.edu/sites/g/files/sbiybj9936/f/slides-bpase-2018.pdf)).
* [Scale by the Bay 2018 presentation](https://youtu.be/M4XnDrRIKx8) that illustrates formal verification of Simplicity in Agda. ([slides](https://lists.ozlabs.org/pipermail/simplicity/2018/000011.html))

## Contact

Interested parties are welcome to join the [Simplicity mailing list](https://lists.ozlabs.org/listinfo/simplicity).
Issues and pull-requests can be made through GitHub's interface.

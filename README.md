# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Build

### Building with Nix

Software artifacts can be built using [Nix](https://nixos.org/nix/).

* To build the Haskell project, run `nix-build -A haskell`.
* To use the Haskell project, try `nix-shell -p "(import ./default.nix {}).haskellPackages.ghcWithPackages (pkgs: [pkgs.Simplicity])"`.
* To build the Coq project, run `nix-build -A coq`.
* For a Simplicity-Haskell development environment, type `nix-shell --arg coq false`.
* Typing `nix-shell` will provide a full C, Coq and Haskell development environment.

### Building the C project manually

Install the [GNU Compiler Collection](https://gcc.gnu.org/) and [GNU Make](https://www.gnu.org/software/make/).
Binary packages are available for Debian (`apt install gcc make`) and other Linux distributions.

1. Open a command line.
1. Change directory to the `C` directory of this repository.
1. To run tests: `make check`
1. To install globally: `make install`
1. To install locally: `make install out=/path/to/dir`
1. To remove generated files: `make clean`

### Building the Coq project manually

Requires [Coq 8.16.1](https://coq.inria.fr/),
[CompCert 3.12](http://compcert.inria.fr/)
and [VST 2.12](https://vst.cs.princeton.edu/).
Packages in the Coq ecosystem are managed by the [opam package manager](https://opam.ocaml.org/).

#### Installing Coq

1. Install `opam` using your distribution's package manager.
1. `opam init`
1. `eval $(opam env)`
1. `opam pin -j$(nproc) add coq 8.16.1`

#### Optional: Installing CoqIDE

[CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) is a user-friendly GUI for writing proofs in Coq.

1. `opam install -j$(nproc) coqide`

#### Installing CompCert

1. `opam repo add coq-released https://coq.inria.fr/opam/released`
1. `opam install -j$(nproc) coq-compcert.3.12`

#### Installing VST

We need a custom build and **cannot** use opam for this step.

1. `wget -O - https://github.com/PrincetonUniversity/VST/archive/v2.12.tar.gz | tar -xvzf -`
1. `cd VST-2.12`
1. `make -j$(nproc) default_target sha`
1. `make install`
1. `install -d $(coqc -where)/user-contrib/sha`
1. `install -m 0644 -t $(coqc -where)/user-contrib/sha sha/*.v sha/*.vo`

#### Building the Simplicity Coq library

1. Change into the `Coq` directory of this repository
1. `coq_makefile -f _CoqProject -o CoqMakefile`
1. `make -f CoqMakefile -j$(nproc)`

#### Optional: Installing the library

1. `make -f CoqMakefile install`

### Building the Haskell project manually

Install the [Glasgow Haskell Compiler](https://www.haskell.org/ghc/) and [Cabal](https://www.haskell.org/cabal/).
Binary packages are available for Debian (`apt install ghc cabal-install`) and other Linux distributions.

1. Open a command line.
1. Change directory to the root directory of this repository.
1. `cabal repl Simplicity`
1. Cabal will build the project and open a GHCi prompt.
    
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

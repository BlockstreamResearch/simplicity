# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A C implementation of a minimal, consensus-critical Simplicity runtime for full nodes.
* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Haskell code generator that exports Simplicity constants to C and Rust.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Build

Use [Nix](https://nixos.org) for the easiest build. Alternatively, use GNU Autotools.

### C project

#### Nix

Change into the root directory of this repository.

Build the nix package.

```bash
nix-build -A c
```

Enter a nix shell to develop the project manually (see below).

```bash
nix-shell --arg coq false --arg haskell false
```

Use arguments to enable / disable the other projects.

#### Manual

Change into the C directory of this repository.

Build the project using make.

```bash
make -j$(nproc)
```

To install the project, run make.

```
make install # use "out=/path/to/dir" for local install
```

To run the tests, run make.

```bash
make check
```

### Haskell project

#### Nix

Change into the root directory of this repository.

Build the nix package.

```bash
nix-build -A haskell
```

Enter a nix shell to develop the project manually (see below).

```bash
nix-shell --arg c false --arg coq false
```

Use arguments to enable / disable the other projects.

#### Manual

Install the [Glasgow Haskell Compiler](https://www.haskell.org/ghc/) and [Cabal](https://www.haskell.org/cabal/).

Change into the root directory of this repository.

Build the project using cabal.

```bash
cabal build
```

To run tests, run cabal.

```bash
cabal test # use --test-options="+RTS -N -RTS" for parallel jobs
```

To enter an interactive GHCi prompt with the project loaded, run cabal.

```bash
cabal repl Simplicity
```

### Coq project

#### Nix

Change into the root directory of this repository.

Build the nix package.

```bash
nix-build -A coq
```

Enter a nix shell to develop the project manually (see below).

The shell provides Coq, CompCert and VST.

```bash
nix-shell --arg c false --arg haskell false
```

Use arguments to enable / disable the other projects.

#### Manual

Install the [opam package manager](https://opam.ocaml.org/).

Enter the opam environment in your shell.

```bash
opam init
eval $(opam env)
```

Install the [Coq theorem prover](https://coq.inria.fr/).

```bash
opam pin -j$(nproc) add coq 8.16.1
```

Install the [CompCert certified C compiler](https://compcert.org/).

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -j$(nproc) coq-compcert.3.12
```

Install a custom version of the [Verified Software Toolchain](https://vst.cs.princeton.edu/).

**You cannot use opam for this step!**

```
wget -O - https://github.com/PrincetonUniversity/VST/archive/v2.12.tar.gz | tar -xvzf -
cd VST-2.12
make -j$(nproc) default_target sha
make install
install -d $(coqc -where)/user-contrib/sha
install -m 0644 -t $(coqc -where)/user-contrib/sha sha/*.v sha/*.vo
```

Enter the Coq directory of this repository.

Build the project using make.

```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile -j$(nproc)
```

To install the project, run make.

```bash
make -f CoqMakefile install
```

## Documentation

Detailed documentation can be found in the `Simplicity-TR.tm` TeXmacs file.
A recent PDF version can be found in the [pdf](https://github.com/ElementsProject/simplicity/blob/pdf/Simplicity-TR.pdf) branch.

## Further Resources

* Our [paper that originally introduced Simplicity](https://arxiv.org/abs/1711.03028).  Some of the finer details are out of date, but it is still a good introduction.
* [BPASE 2018 presentation](https://youtu.be/VOeUq3oR2fk) of the above paper ([slides](https://cyber.stanford.edu/sites/g/files/sbiybj9936/f/slides-bpase-2018.pdf)).
* [Scale by the Bay 2018 presentation](https://youtu.be/M4XnDrRIKx8) that illustrates formal verification of Simplicity in Agda ([slides](https://lists.ozlabs.org/pipermail/simplicity/2018/000011.html)).
* Our library [rust-simplicity](https://github.com/BlockstreamResearch/rust-simplicity) that implements Simplicity in Rust.

## Contact

Interested parties are welcome to join the [Simplicity mailing list](https://lists.ozlabs.org/listinfo/simplicity).
Issues and pull-requests can be made through GitHub's interface.

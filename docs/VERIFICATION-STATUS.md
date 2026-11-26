# Formal verification status

This is the detailed reference for the formal verification of Simplicity: what
each goal covers, where existing proofs are, and the conditions and known
mismatches that limit them. For an overview of the goals and how they depend
on each other, see the [verification roadmap](VERIFICATION.md).

## Formal specification of Simplicity and the Bit Machine

### Denotational semantics of Simplicity

**Status:** Done for core Simplicity and its extensions, in `Coq/Simplicity/`
(`Core.v`, `Alg.v`, `Primitive.v`, `Delegation.v`, `MerkleRoot.v`). The only
blockchain primitives modeled are an early Bitcoin set; see
[Coq model of the transaction environment](#coq-model-of-the-transaction-environment). `Core.v` also proves that every function
between finite types can be expressed in core Simplicity
(`Simplicity_Completeness`).

### Bit Machine specification

**Status:** Done, in `Coq/Simplicity/BitMachine.v`.

### Correctness of translation from Simplicity to the Bit Machine

This includes the tail-call-optimized (TCO) translation that the C evaluator
uses, and the static memory bounds for that translation, including for
`disconnect`.

**Status:** For core Simplicity only, the naive translation is proved correct
(`translate_correct` in `Coq/Simplicity/Translate.v`), and
`Coq/Simplicity/StaticAnalysis.v` proves the static memory bound for it. The
extensions (assertions, witnesses, `disconnect`, primitives, and jets) aren't
covered yet, and neither are the TCO translation and its memory bounds.

### Static analysis of cost and frame count

Specifications of the static analyses that bound a program's cost and its
maximum number of Bit Machine frames, with proofs that the bounds hold for
every execution. The spending-condition specification relies on the cost
bound.

### Serialization and type inference

Coq specifications of how programs and witness data are serialized, how types
are inferred, and which encodings are rejected to prevent malleability.

## Formal specification of jets

Each jet is specified by the Simplicity expression it replaces. Verifying a jet
means proving that its C implementation matches a Coq functional specification,
and that this specification equals the denotation of the jet's Simplicity
expression. Jets that read the transaction are specified using the
integration's primitives, which carry its effects, so their specifications
depend on a Coq model of those primitives.

**Status:** `Coq/Simplicity/Word.v` and `Coq/Simplicity/SHA256.v` prove the
Simplicity expressions for word arithmetic and SHA-256 block compression
correct against mathematical specifications. In [`feat/jet-equivalence`](https://github.com/brenorb/simplicity/tree/feat/jet-equivalence),
each jet's specification is a Coq transcription of its Simplicity expression,
and a gate checks the transcriptions against the Haskell sources.

Further goals:

- A library in `Coq/Simplicity/` that specifies every jet by a Simplicity
  expression, which serves as the reference specification for all
  implementations.
- Proofs that the secp256k1 jets give equal outputs for inputs that represent
  the same field element, scalar or point, even when the representations
  differ.
- For every jet, a characterization that proofs about programs can use: a
  statement of what the jet computes, in terms suited to reasoning. For
  example, `add_32` returns the
  sum of its inputs modulo 2^32 together with the carry, and an introspection
  jet returns a given field of the transaction in the Coq environment model.
  `Coq/Simplicity/Word.v` proves characterizations of this kind for the
  adders and multipliers.
- For the minority of jets that implement an external standard, a proof that
  the specification matches it: for example, SHA-256, BIP 340, the secp256k1
  group operations, BIP 341, and the timelock rules of BIPs 65, 68, and 113.
  `Coq/Simplicity/SHA256.v` does this for SHA-256 block compression.
- Bounds on the number of execution steps of each jet's C code, to support
  the cost assigned to the jet.

## Verification of C jet implementations against CompCert C semantics

The proofs use VST, which reasons about CompCert C semantics. Production builds
use other compilers, which are trusted; see
[Trusted components](#trusted-components).

**Status:** On master, `Coq/C/secp256k1/` verifies libsecp256k1's int128
helpers and `modinv64`. In [`feat/jet-equivalence`](https://github.com/brenorb/simplicity/tree/feat/jet-equivalence), AI agents
covered all 533 C jet functions (core, Elements and Bitcoin) for the C sources
at commit `e3b6701` on x86-64 Linux. Each one has either a proof that it
conforms to its specification, in some cases under the conditions below, or a
proof that it doesn't:

- Most proofs are unconditional.
- Many depend on models of `memcpy`, `memset`, `memcmp` or `__builtin_ctzl`,
  which CompCert doesn't specify.
- `output_is_fee`, `total_fee` and `hash_to_curve` depend on unproven
  properties of SHA-256 that their specifications don't state. If SHA-256
  behaves like a random oracle, the fee jets' property is almost certainly
  false and the `hash_to_curve` property may or may not hold, but finding a
  counterexample to either is infeasible.
- The proofs assume that the C data structures holding the transaction and
  the Bit Machine frames correctly represent the model's values. Proving that
  the C code builds them correctly belongs to the integration work below. The
  branch's review notes also list a few memory-layout predicates that exclude
  extreme but valid addresses.

Each theorem is about a single call of a jet's C function. It states that the
call terminates without any observable events (CompCert's empty event trace),
and the branch proves that Clight execution is deterministic, so this is the
only execution. The theorems don't bound the number of steps, and they don't
say anything about the evaluator's execution between jet calls.

The current counts are in `Coq/C/JET_PROOF_BACKLOG.md` on that branch.

Separately from the proofs, the Haskell test suite's "C / SPEC" tests
(`Haskell/Tests/Simplicity/FFI/Tests.hs` and the Elements and Bitcoin
`FFI/Tests.hs`) compare each C jet with its Haskell specification on random
inputs, including random transaction environments for the introspection jets.

### secp256k1 field, scalar, and group jets, including the libsecp256k1 code they call

- Both the int128 proofs on master and the branch's proofs cover
  libsecp256k1's int128 struct emulation (the branch undefines
  `__SIZEOF_INT128__` to select it). GCC and Clang builds use native
  `__int128` instead, so that code path isn't covered, and neither are
  platforms other than the target.
- `gej_ge_add_ex` is proved *not* to conform: for some inputs with a
  noncanonical Y coordinate (a word at least the field modulus p), the
  specification outputs the ratio unnormalized, while the C code normalizes
  it. The two outputs encode the same field element. Because the C
  behavior is consensus on Liquid, the specification will change to match
  the C code. A jet's CMR is computed from its cost and the identity Merkle
  root of its specification, so this jet's CMR will be kept at its current
  value instead of being computed from the new specification, so that
  existing programs keep working.

### Transaction introspection jets

- The Bitcoin jet proofs that read the transaction quantify over the
  transactions that `Coq/Simplicity/Primitive/Bitcoin.v` can represent. That
  model defines the fee as total output minus total input and requires it to
  be nonnegative, the reverse of the Haskell definition, so the only valid
  Bitcoin transactions it can represent have a fee of zero. The error is
  only in the model: the Haskell specification and the C code agree with each
  other and with Bitcoin. The proofs reportedly go through with the model
  corrected, but that version isn't on the branch yet. They could instead
  be redone against a model of the current Bitcoin integration's
  primitives. The model also spells the `LockTime` primitive's name
  differently from the Haskell library (`"locktime"` instead of
  `"lockTime"`), so its commitment tag differs.
- The Elements jet proofs use the branch's own port of the Haskell
  environment definitions (`Coq/C/jet_elements_prim.v`). It admits every
  environment that the Haskell definitions do, but it hasn't been reviewed
  against the Haskell sources.

## Correctness of the C evaluator with respect to the Bit Machine specification

The C evaluator refines the Bit Machine specification: it implements the TCO
translation, and it can fail where the specification doesn't, for example by
exceeding resource limits.

## Correctness of the C decoder and type inference

The C functions that deserialize programs and witness data and infer types,
proved against the serialization and type inference specifications, including
rejection of every encoding that the specifications rule out.

**Status:** No proofs. The Haskell serialization tests check, for each jet,
that the C code decodes it and assigns it the same CMR and cost as the Haskell
library. These CMRs and costs are generated from the Haskell library by
`Haskell-Generate`. rust-simplicity's `c_rust_merkle` fuzz
target compares whole-program decoding and type checking between the C and
Rust implementations.

## Integration with `elementsd` and `bitcoind`

The goal is a formal specification of each integration, with proofs that the
implementation conforms to it. The specification covers every check that a
node performs on a tapleaf that contains a Simplicity program. The parts in the
Simplicity library can be proved in Coq. The parts in the node's C++ code,
such as reading the witness stack and computing the budget, are stated as an
interface contract.

### Specification of a satisfied spending condition

A statement of when a Simplicity program and its witness satisfy a Taproot
spending condition in a transaction. An input is valid if and only if its
program decodes, its commitment Merkle root matches the leaf committed by the
control block, its witness data decodes, its cost falls within the bounds
that the node derives from the witness weight, its denotation succeeds in the
environment derived from the transaction, and it passes the anti-DoS checks:
every node that isn't hidden is executed, and every `case` executes both of
its branches.

This specification is what proofs about individual programs connect to: see
[Verification of program properties](#verification-of-program-properties).

### Correctness of transaction environment construction

The C functions that convert the node's raw transaction and Taproot data into
the environment that jets read (`simplicity_elements_mallocTransaction` and
`simplicity_elements_mallocTapEnv`, with their Bitcoin equivalents), including
the hashes they precompute.

### Correctness of the top-level entry point

The C functions that compose decoding, type inference, Merkle root checks, cost
analysis, and evaluation (`simplicity_elements_execSimplicity` and its Bitcoin
equivalent), proved against the spending-condition specification.

### Node-side requirements

The preconditions that the node's C++ code must meet when it calls the library:
how it extracts the program, witness, and control block from the witness stack,
how it fills the raw transaction structures, how it computes the budget, and how
it maps error codes to script validation results. VST doesn't verify C++, so
these are stated as an interface contract.

### Security properties of the integration

Properties that users rely on, beyond the spending condition itself. Examples:
a revealed program whose commitment Merkle root matches the committed leaf is
the program that was committed to, and `sig_all_hash` commits to every part
of the transaction that it describes. These depend on cryptographic
assumptions; see [Cryptographic assumptions](#cryptographic-assumptions).

## Cryptographic assumptions

Most results so far haven't needed any cryptographic assumption, because they
prove that one computation equals another. Assumptions become necessary when a
statement is about security: about which program was committed to, who
authorized a spend, or what a signature covers. This first happens in the
security properties of the integrations and in properties of programs that
check signatures or hashes.

An axiom such as "SHA-256 has no collisions" is false, so it can't be stated
directly in Coq. One workable approach is a reduction theorem, which proves
that any violation of the property yields an explicit collision, second
preimage, or signature forgery. The conditional fee-jet results on
`feat/jet-equivalence` take this form. Probabilistic statements, such as
unforgeability, need a framework for game-based cryptographic proofs, such as
SSProve or FCF in Coq.

## Trusted components

The proofs trust the following components, and verifying them is out of
scope:

- The C compiler used for production builds, such as GCC or Clang. The proofs
  are about CompCert's C semantics, and production builds aren't compiled with
  CompCert.
- The standard C library functions that the code calls, such as `memcpy`,
  `memset`, and `memcmp`, and compiler builtins such as `__builtin_ctzl`. The
  proofs model each one by its documented contract: the C standard for library
  functions, and the compiler's documentation for builtins. Production
  implementations of these functions are typically hand-written assembly,
  selected at run time for the CPU, and compilers often replace small calls
  with inline code. Proving them would require separate proofs for each
  platform and library version, and the compiler would still be trusted.
- Coq's kernel, and the CompCert C semantics and VST program logic that the
  proofs are stated in.
- The node's C++ code that calls the Simplicity library, which is trusted to
  meet the interface contract described in
  [Node-side requirements](#node-side-requirements).
- The rest of each node implementation (`elementsd`, and Bitcoin
  Inquisition's `bitcoind`): its other consensus rules, including the check
  that a tapleaf is committed in the output key and the enforcement of
  timelocks, along with transaction parsing and the UTXO set. The goal is to
  specify and verify only what each integration adds to its node.

The library-function models remain in scope. Each proof must establish the
model's preconditions at every call site, such as valid and non-overlapping
ranges for `memcpy`. The models themselves need review, to make sure that
they don't assume more than the documented contracts guarantee.

Because the rest of the node is trusted, a property of a program is a
statement about which transactions satisfy its spending condition. Whether
such a transaction is confirmed, and in what order relative to other
transactions, depends on consensus rules outside the integration. For
example, `check_lock_distance` checks an input's sequence number, and the
node delays confirmation by enforcing BIP 68. Properties spanning
multiple transactions also assume that those rules are enforced, for example
that an output can't be spent twice.

## Bitcoin Inquisition integration: jet specifications and verification

This covers the version of Simplicity integrated into Bitcoin Inquisition, a
fork of Bitcoin Core, which runs on a signet that supports Simplicity. It
differs from the version that runs on Elements.

**Status:** [`feat/jet-equivalence`](https://github.com/brenorb/simplicity/tree/feat/jet-equivalence)
covers the Bitcoin jets in `C/bitcoin/` as of commit `e3b6701`. Bitcoin
Inquisition's copy of the Simplicity library has the same jets, and its jet
code is identical to that commit.

## Agreement of rust-simplicity with the specification

SimplicityHL and most tools build, encode, and analyze programs with
[rust-simplicity](https://github.com/BlockstreamResearch/rust-simplicity).
It calls the C library's jets, but implements its own versions of Merkle root
computation, serialization, type inference, cost analysis, and the Bit
Machine. If any of these disagrees with the C library, users can commit funds
to a program that the node will reject or compute differently. This needs
either proofs against the Coq specifications or systematic differential
testing against the C library.

**Status:** The fuzz target `fuzz/fuzz_targets/c_rust_merkle.rs` checks that
Rust and C agree on whether Elements programs decode and type-check, and on
their Merkle roots. A few unit tests (`check_merkle_roots` in
`src/node/mod.rs`) also check costs against fixed expected values. Evaluation
and cost analysis aren't compared systematically.

## SimplicityHL

SimplicityHL is developed in the
[SimplicityHL repository](https://github.com/BlockstreamResearch/SimplicityHL).

### SimplicityHL language specification

The type system and semantics of SimplicityHL.

### SimplicityHL compiler correctness

For every well-typed SimplicityHL program, the denotation of the compiled
Simplicity program equals the program's SimplicityHL semantics.

## Verification of correctness of optimizations

Some optimizations could be performed by the SimplicityHL compiler and could
be proven correct there relative to a SimplicityHL specification. Other
optimizations could be performed in low-level Simplicity after compilation
and could be proven correct relative to the Simplicity specification.

## Verification of program properties

Proofs that a particular Simplicity or SimplicityHL program behaves as
intended, for example that an output can only be spent by a transaction that
pays to a given address. Contract authors use these proofs to establish that
their own programs do what they intend. Together with the spending-condition
specification and the integration proofs, a property of a program's
denotation becomes a property of which transactions the node accepts.

Proofs about a program's denotation can start before the rest of the roadmap
is finished. Connecting them to node behavior requires the integration
sections, connecting proofs about SimplicityHL source to deployed programs
requires compiler correctness, and properties that read the transaction
require the environment model below.

A property of a committed program must hold for every witness and for every
expression that a spender can supply through `disconnect`. Properties that
involve signatures are stated relative to signature verification, for example
"the program succeeds only if it receives a valid signature under key K". What
such a property guarantees in practice depends on the signature scheme being
unforgeable.

### Coq model of the transaction environment

A specification of the Elements and Bitcoin transaction environments suited to
program proofs, with lemmas that characterize what each introspection jet
returns. The model should match the primitives' semantics in the Haskell
library (`primSem`). On master, `Coq/Simplicity/Primitive/Bitcoin.v` models an early set of Bitcoin
primitives, with the fee error described in the jet status above, and there
isn't a model of the Elements environment.

### Properties of Simplicity programs

Proofs about the denotation of compiled or hand-written Simplicity programs.
Properties that don't depend on the transaction environment can be proved
with the existing semantics; `Coq/Simplicity/Word.v` and
`Coq/Simplicity/SHA256.v` contain examples.

### Properties of SimplicityHL programs

Proofs about SimplicityHL source programs, which carry over to the deployed
Simplicity programs once the compiler is proved correct. Until then, such
properties are proved about the compiled Simplicity program.

### Properties spanning multiple transactions

Properties of contracts that constrain a sequence of spends, such as
covenants and vaults, which require a model of chains of transactions.

### Reusable lemmas and example contracts

A library of lemmas about common program patterns, such as signature checks,
timelocks, and constraints on outputs, together with a few fully verified
example contracts. These let people outside the core team prove properties of
their own programs by adapting existing proofs.

### Verified standard library

Proofs that the functions in the SimplicityHL standard library
([simplicityhl-std](https://github.com/BlockstreamResearch/simplicityhl-std))
behave as documented. Until the compiler is proved correct, these proofs
are about the compiled Simplicity code.

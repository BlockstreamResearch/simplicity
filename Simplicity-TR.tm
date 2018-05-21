<TeXmacs|1.99.2>

<style|book>

<\body>
  <\doc-data|<\doc-title>
    Simplicity
  </doc-title>|<doc-author|<author-data|<author-name|Russell
  O'Connor>|<\author-affiliation>
    Blockstream
  </author-affiliation>|<author-email|roconnor@blockstream.com>>>>
    \;
  </doc-data>

  <\table-of-contents|toc>
    <vspace*|1fn><with|font-series|bold|math-font-series|bold|1<space|2spc>Introduction>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-1><vspace|0.5fn>

    1.1<space|2spc>Design Goals <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-2>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|2<space|2spc>Core
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-3><vspace|0.5fn>

    2.1<space|2spc>Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-4>

    <with|par-left|1tab|2.1.1<space|2spc>Abstract Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-5>>

    <with|par-left|2tab|2.1.1.1<space|2spc>Formal Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>>

    <with|par-left|1tab|2.1.2<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-7>>

    <with|par-left|2tab|2.1.2.1<space|2spc>Formal Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-8>>

    2.2<space|2spc>Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-9>

    <with|par-left|1tab|2.2.1<space|2spc>Identity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-10>>

    <with|par-left|1tab|2.2.2<space|2spc>Composition
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-11>>

    <with|par-left|1tab|2.2.3<space|2spc>Constant Unit
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-12>>

    <with|par-left|1tab|2.2.4<space|2spc>Left Injection
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-13>>

    <with|par-left|1tab|2.2.5<space|2spc>Right Injection
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-14>>

    <with|par-left|1tab|2.2.6<space|2spc>Case
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-15>>

    <with|par-left|1tab|2.2.7<space|2spc>Pair
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-16>>

    <with|par-left|1tab|2.2.8<space|2spc>Take
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-17>>

    <with|par-left|1tab|2.2.9<space|2spc>Drop
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-18>>

    <with|par-left|1tab|2.2.10<space|2spc>Formal Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-19>>

    <with|par-left|1tab|2.2.11<space|2spc>Formal Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-20>>

    2.3<space|2spc>Example Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-21>

    <with|par-left|1tab|2.3.1<space|2spc>Bit Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-22>>

    <with|par-left|1tab|2.3.2<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-23>>

    <with|par-left|1tab|2.3.3<space|2spc>Bitwise Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-24>>

    <with|par-left|1tab|2.3.4<space|2spc>SHA-256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-25>>

    <with|par-left|1tab|2.3.5<space|2spc>Modular Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26>>

    <with|par-left|1tab|2.3.6<space|2spc>Elliptic Curve Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27>>

    2.4<space|2spc>Completeness Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28>

    2.5<space|2spc>Operational Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-29>

    <with|par-left|1tab|2.5.1<space|2spc>Repesenting Values as Cell Arrays
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|1tab|2.5.2<space|2spc>Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    <with|par-left|2tab|2.5.2.1<space|2spc>Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>>

    <with|par-left|2tab|2.5.2.2<space|2spc>Active Write Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <with|par-left|2tab|2.5.2.3<space|2spc>Active Read Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    <with|par-left|2tab|2.5.2.4<space|2spc>Abort Instruction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-36>>

    <with|par-left|2tab|2.5.2.5<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>>

    <with|par-left|2tab|2.5.2.6<space|2spc>Crashing the Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-38>>

    <with|par-left|1tab|2.5.3<space|2spc>Executing Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39>>

    <with|par-left|2tab|2.5.3.1<space|2spc>Tail Composition Optimisation
    (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-40>>

    2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-41>

    <with|par-left|1tab|2.6.1<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-42>>

    <with|par-left|2tab|2.6.1.1<space|2spc>Maximum Cell Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-43>>

    <with|par-left|2tab|2.6.1.2<space|2spc>Maximum Frame Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>>

    <with|par-left|1tab|2.6.2<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-45>>

    2.7<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46>

    2.8<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>

    <with|par-left|1tab|2.8.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Simplicity
    Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49><vspace|0.5fn>

    3.1<space|2spc>Monadic Effects <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>

    <with|par-left|1tab|3.1.1<space|2spc>Kleisli Morphisms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51>>

    <with|par-left|1tab|3.1.2<space|2spc>Cartesian Strength
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52>>

    <with|par-left|1tab|3.1.3<space|2spc>Monadic Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53>>

    <with|par-left|2tab|3.1.3.1<space|2spc>Identity Monad
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54>>

    3.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55>

    <with|par-left|1tab|3.2.1<space|2spc>Witness Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56>>

    <with|par-left|1tab|3.2.2<space|2spc>Serialization with Witnesses
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57>>

    <with|par-left|1tab|3.2.3<space|2spc>Type Inference with Witness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58>>

    3.3<space|2spc>Assertions and Failure
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-59>

    <with|par-left|1tab|3.3.1<space|2spc>Monad Zero
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-60>>

    <with|par-left|1tab|3.3.2<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-61>>

    <with|par-left|2tab|3.3.2.1<space|2spc>Option Monad
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-62>>

    <with|par-left|1tab|3.3.3<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-63>>

    <with|par-left|2tab|3.3.3.1<space|2spc>Pruning Unused
    <with|font-family|ss|case> Branches <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-64>>

    <with|par-left|2tab|3.3.3.2<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-65>>

    3.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-66>

    <with|par-left|1tab|3.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-67>>

    <with|par-left|2tab|3.4.1.1<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-68>>

    <with|par-left|2tab|3.4.1.2<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-69>>

    3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-70>

    <with|par-left|1tab|3.5.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-71>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Jets>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-72><vspace|0.5fn>

    4.1<space|2spc>Example: The Standard Single Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-73>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Delegation>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-74><vspace|0.5fn>

    5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-75>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-76><vspace|0.5fn>

    6.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-77>

    6.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-78>

    <with|par-left|1tab|6.2.1<space|2spc>The ``Initial'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-79>>

    <with|par-left|1tab|6.2.2<space|2spc>The ``Final'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-80>>

    <with|par-left|2tab|6.2.2.1<space|2spc>Simplicity Algebras
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-81>>

    <with|par-left|2tab|6.2.2.2<space|2spc>The ``Final'' Representation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-82>>

    <with|par-left|2tab|6.2.2.3<space|2spc>Constructing ``Final'' Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-83>>

    <with|par-left|1tab|6.2.3<space|2spc>Why two representations of Terms?
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-84>>

    6.3<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-85>

    <with|par-left|1tab|6.3.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-86>>

    <with|par-left|1tab|6.3.2<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-87>>

    6.4<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-88>

    <with|par-left|1tab|6.4.1<space|2spc>Bit Machine Code
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-89>>

    <with|par-left|2tab|6.4.1.1<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-90>>

    <with|par-left|1tab|6.4.2<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-91>>

    <with|par-left|1tab|6.4.3<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-92>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-93><vspace|0.5fn>

    7.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-94>

    7.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-95>

    7.3<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-96>

    <with|par-left|1tab|7.3.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-97>>

    <with|par-left|1tab|7.3.2<space|2spc>Multi-bit Words
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-98>>

    <with|par-left|2tab|7.3.2.1<space|2spc>Arithmetic operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-99>>

    <with|par-left|2tab|7.3.2.2<space|2spc>Bit-wise operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-100>>

    <with|par-left|1tab|7.3.3<space|2spc>Generic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-101>>

    <with|par-left|1tab|7.3.4<space|2spc>SHA-256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-102>>

    7.4<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-103>

    <with|par-left|1tab|7.4.1<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-104>>

    <with|par-left|1tab|7.4.2<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-105>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-106><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    A<space|2spc>Notation> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-107><vspace|0.5fn>

    A.1<space|2spc>Algebraic Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-108>

    <with|par-left|1tab|A.1.1<space|2spc>Option Type
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-109>>

    A.2<space|2spc>Records <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-110>

    A.3<space|2spc>Lists <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-111>

    A.4<space|2spc>Byte Strings <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-112>
  </table-of-contents>

  <chapter|Introduction>

  <with|color|red|TODO: specify commitment and redemption time.>

  <section|Design Goals>

  <chapter|Core Simplicity>

  Simplicty is a typed functional programming language based on Gentzen's
  sequent calculus. The core language consists of nine combinators for
  forming expressions. These nine combinators capture the computational power
  of Simplicity. In later chapters, other combinators will extend this core
  language and provide other effects to handle input and access the
  transaction that provides context for the program.

  <section|Types>

  This section introduces the abstract syntax and semantics types available
  in Simplicity.

  <subsection|Abstract Syntax>

  <assign|1|<math|<with|font|Bbb*|1>>>Simplicity operates over three kinds of
  types:

  <\itemize-minus>
    <item>The unit type, written as <value|1>.

    <item>The sum (also known as the disjoint union) of two types, witten as
    <math|A + B>.

    <item>The product of two types, written as <math|A\<times\>B>.
  </itemize-minus>

  <subsubsection|Formal Syntax>

  Formally we define the abstract syntax of types as an inductive type in
  Coq:

  <\render-code>
    <\verbatim>
      <strong|Inductive> Ty : Set :=

      \| Unit : Ty

      \| Sum \ : Ty -\<gtr\> Ty -\<gtr\> Ty

      \| Prod : Ty -\<gtr\> Ty -\<gtr\> Ty.
    </verbatim>
  </render-code>

  <subsection|Denotational Semantics>

  <assign|injl-long|<macro|A|B|x|<math|\<sigma\><rsup|\<b-up-L\>><rsub|<arg|A>,<arg|B>><arg|x>>>><assign|injr-long|<macro|A|B|x|<math|\<sigma\><rsup|\<b-up-R\>><rsub|<arg|A>,<arg|B>><arg|x>>>><assign|pair-long|<macro|x|y|A|B|<math|<around*|\<langle\>|<arg|x>,<arg|y>|\<rangle\>><rsub|<arg|A>,<arg|B>>>>><assign|injl|<macro|x|<math|\<sigma\><rsup|\<b-up-L\>><arg|x>>>><assign|injr|<macro|x|<math|\<sigma\><rsup|\<b-up-R\>><arg|x>>>>The
  unit type has a single value which we write
  <math|<around*|\<langle\>||\<rangle\>>> or as
  <math|<around*|\<langle\>||\<rangle\>>:<value|1>> if we include its type
  annotation.

  The type <math|A + B> contains values which are the tagged union of values
  from <math|A> and <math|B>. The sum type has left-tagged values
  <math|<injl-long|A|B|<around*|(|a|)>>:A+ B> for each value <math|a : A>,
  and right-tagged values <math|<injr-long|A|B|<around*|(|b|)>>:A+ B> for
  each value <math|b : B>.

  The type <math|A\<times\>B> contains pairs of values from <math|A> and
  <math|B>. For each pair of values <math|a :A> and <math|b : B> there is
  value <math|>for the pair written as <math|><pair-long|a|b|A|B>.

  Simplicity has neither function types nor recursive types. Every type in
  Simplicity can only contain a finite number of values. For example, the
  type <math|<value|1>+<value|1>> has exactly two values, namely
  <injl-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>> and
  <injr-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>. The type
  <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  has exactly four values. As you can see, the number of values that a type
  contains can be easily calculated by interpreting the type as an arithmetic
  expression. Be aware that these types are not arithmetic expressions. For
  example, the types <math|<around*|(|<value|1>+<value|1>|)>+<around*|(|<value|1>+<value|1>|)>>
  and <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  are distinct and not interchangable.

  The type annotations on values can often be infered and are tedious to
  write out. Therefore we will usually omit the annotations, writing
  <math|<injl-long|A|B|<around*|(|a|)>>> as <math|<injl|<around*|(|a|)>>>,
  <injr-long|A|B|<around*|(|b|)>> as <math|<injr|<around*|(|b|)>>>, and
  <math|<pair-long|a|b|A|B>> as <math|<around*|\<langle\>|a,b|\<rangle\>>>.
  We will reserve the fully annotated versions for the rare cases where the
  annotations are ambigous or where we want to draw specific attention to
  them.

  <subsubsection|Formal Semantics>

  Formally we define the denotational semantics as a function from syntax to
  types from the standard library in Coq:

  \;

  <\verbatim>
    Fixpoint tySem (X : Ty) : Set :=

    match X with

    \| Unit =\<gtr\> Datatypes.unit

    \| Sum A B =\<gtr\> tySem A + tySem B

    \| Prod A B =\<gtr\> tySem A * tySem B

    end.
  </verbatim>

  <section|Terms>

  Simplicity programs are composed of terms that denote functions between
  types. Every Simplicity term is associated with an input type and an output
  type and we write a type annotated term as <math|t:A\<vdash\>B> where
  <math|t> is the term, <math|A> is the input type and <math|B> is the output
  type. We write <math|<around*|\<llbracket\>|t|\<rrbracket\>>\<of\>A\<rightarrow\>B>
  for the function that the term <math|t> denotes.

  Core Simplicty has nine combinators for forming well-typed terms.

  <subsection|Identity>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|iden><rsub|A>
    : A\<vdash\>A>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<samp|iden><rsub|A>>|\<rrbracket\>><around*|(|a|)>\<assign\>a
  </equation*>

  For every type <math|A> there we have an identity term that denotes the
  identity function for that type.\ 

  Like the type annotations on values, the type argument for <math|iden>
  usually can be infered and therefore we will usually omit (as we did for
  the denotation equation above). Similarly, we will usually omit the type
  arguments for all the other Simplicity combinators.

  <subsection|Composition>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : B\<vdash\>C>>>>>>>>|<row|<cell|<math|<math-ss|comp><rsub|A,B,C> s t:
    A\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|comp><rsub|A,B,C>> s
    t|\<rrbracket\>><around*|(|a|)>\<assign\><around*|(|<around*|\<llbracket\>|t|\<rrbracket\>>\<circ\><around*|\<llbracket\>|s|\<rrbracket\>>|)><around*|(|a|)>
  </equation*>

  The composition combinator functionally composes its two arguments,
  <math|s> and <math|t>, when the output type of <math|s> matches the input
  type of <math|t>.

  <subsection|Constant Unit>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<math-ss|unit><rsub|A>
    : A\<vdash\><value|1>>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|unit><rsub|A>>|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<langle\>||\<rangle\>>
  </equation*>

  The constant unit term ignores its argument and always returns
  <math|<around*|\<langle\>||\<rangle\>>>, the unique value of the unit type.
  Since the argument is ignored, we have a constant unit term for every type.

  <subsection|Left Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>B>>>|<row|<cell|<math|<math-ss|injl><rsub|A,B,C>
    t: A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|injl><rsub|A,B,C>>
    t|\<rrbracket\>><around*|(|a|)>\<assign\><injl|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The left injection combinator composes a left-tag with its argument
  <math|t>.

  <subsection|Right Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>C>>>|<row|<cell|<math|<math-ss|injr><rsub|A,B,C>
    t: A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|injr><rsub|A,B,C>>
    t|\<rrbracket\>><around*|(|a|)>\<assign\><injr|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The right injection combinator composes a right-tag with its argument
  <math|t>.

  <subsection|Case>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<times\>C\<vdash\>D>>|<cell|<math|t
    : B\<times\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|case><rsub|A,B,C,D>
    s t: <around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math|<math-ss|case><rsub|A,B,C,D>>
    s t|\<rrbracket\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math|<math-ss|case><rsub|A,B,C,D>>
    s t|\<rrbracket\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|\<langle\>|b,c|\<rangle\>>>>>>
  </eqnarray*>

  The case combinator is Simplicity's only branching operation. Given a pair
  of values with the first component being a sum type, this combinator
  evalutes either its <math|s> or <math|t> argument depending on which tag
  the first component has, on the pair of inputs.

  <subsection|Pair>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : A\<vdash\>B>>>>>>>>|<row|<cell|<math|<math-ss|pair><rsub|A,B,C> s t:
    A\<vdash\>B\<times\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|pair><rsub|A,B,C>> s
    t|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<langle\>|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>,<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|\<rangle\>>
  </equation*>

  The pair combinator executes both its arguments, <math|s> and <math|t>, on
  the same input and returns the pair of the two results.

  <subsection|Take>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>C>>>|<row|<cell|<math|<math-ss|take><rsub|A,B,C>
    t: A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|take><rsub|A,B,C>>
    t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>
  </equation*>

  The take combinator denotes a function on pairs that passes its first
  component to <math|t> and ignores its second component.

  <subsection|Drop>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:B\<vdash\>C>>>|<row|<cell|<math|<math-ss|drop><rsub|A,B,C>
    t: A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|drop><rsub|A,B,C>>
    t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>><around*|(|b|)>
  </equation*>

  The drop combinator denotes a function on pairs that passes its second
  component to <math|t> and ignores its first component.

  <subsection|Formal Syntax>

  We define the formal syntax of well-typed core Simplicity terms as an
  inductive family in Coq:

  <\render-code>
    <\verbatim>
      <strong|Inductive> Term : Ty -\<gtr\> Ty -\<gtr\> Set :=

      \| iden : forall {A}, Term A A

      \| comp : forall {A B C}, Term A B -\<gtr\> Term B C -\<gtr\> Term A C

      \| unit : forall {A}, Term A Unit

      \| injl : forall {A B C}, Term A B -\<gtr\> Term A (Sum B C)

      \| injr : forall {A B C}, Term A C -\<gtr\> Term A (Sum B C)

      \| case : forall {A B C D},

      \ \ \ \ Term (Prod A C) D -\<gtr\> Term (Prod B C) D -\<gtr\> Term
      (Prod (Sum A B) C) D

      \| pair : forall {A B C}, Term A B -\<gtr\> Term A C -\<gtr\> Term A
      (Prod B C)

      \| take : forall {A B C}, Term A C -\<gtr\> Term (Prod A B) C

      \| drop : forall {A B C}, Term B C -\<gtr\> Term (Prod A B) C.
    </verbatim>
  </render-code>

  <subsection|Formal Semantics>

  The formal semantics in Coq for core Simplicity recursively interprets each
  term as a function between the formal semantics of its associated types:

  \;

  <\verbatim>
    Fixpoint eval {A B} (x : Term A B) : tySem A -\<gtr\> tySem B :=

    match x in Term A B return tySem A -\<gtr\> tySem B with

    \| iden =\<gtr\> fun a =\<gtr\> a

    \| comp s t =\<gtr\> fun a =\<gtr\> eval t (eval s a)

    \| unit =\<gtr\> fun _ =\<gtr\> tt

    \| injl t =\<gtr\> fun a =\<gtr\> inl (eval t a)

    \| injr t =\<gtr\> fun a =\<gtr\> inr (eval t a)

    \| case s t =\<gtr\> fun p =\<gtr\> let (ab, c) := p in

    \ \ \ \ match ab with

    \ \ \ \ \| inl a =\<gtr\> eval s (a, c)

    \ \ \ \ \| inr b =\<gtr\> eval t (b, c)

    \ \ \ \ end

    \| pair s t =\<gtr\> fun a =\<gtr\> (eval s a, eval t a)

    \| take t =\<gtr\> fun ab =\<gtr\> eval t (fst ab)

    \| drop t =\<gtr\> fun ab =\<gtr\> eval t (snd ab)

    end.
  </verbatim>

  <section|Example Simplicity>

  Simplicity is not meant as a language to directly write programs in. It is
  intended to be a backend language that some other language (or languages)
  is complied or translated to. However, one can program directly in
  Simplicity just as one can write programs directly in an assembly language.

  Becasue the core Simplicity langauge may seem meager, it is worthwhile to
  see how one can build up sophisticated programs in it.

  <subsection|Bit Operations>

  <assign|2|<with|font|Bbb*|2>>Let us define a type of two values for
  Booleans, or Bit. We will denote this type by <math|<2>>.

  <\equation*>
    <2>\<assign\><value|1>+<value|1>
  </equation*>

  To be clear, we are not doing arithmetic above; we are instead defining the
  type for bit to be the sum type of two unit types.

  We will name the two values of this type, <math|<math-tt|0><rsub|<2>>> and
  <math|<math-tt|1><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-tt|0><rsub|<2>>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|<math-tt|1><rsub|<2>>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>>>>>
  </eqnarray*>

  We can define the terms that represent the constant functions that return
  these two values as <math|<math-ss|false>> and <math|<math-ss|true>>
  respectively

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|false><rsub|A>>|<cell|\<assign\>>|<cell|<math-ss|injl><rsub|A,<value|1>,<value|1>>
    <math-ss|unit> : A\<vdash\><2>>>|<row|<cell|<math-ss|true><rsub|A>>|<cell|\<assign\>>|<cell|<math-ss|injr><rsub|A,<value|1>,<value|1>>
    <math-ss|unit> : A\<vdash\><2>>>>>
  </eqnarray*>

  As a consequence of this these definitions, we can prove that
  <math|<math-ss|false>> and <math|<math-ss|true>> have the following
  semantics.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|false>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|<math-tt|0><rsub|<2>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|<math-tt|1><rsub|<2>>>>>>
  </eqnarray*>

  Next, we define a condition combinator to branch based on the value of a
  bit using <math|<math-ss|case>> and <samp|drop>. The first argument is the
  ``then'' clause and the second argument is the ``else'' clause.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : A\<vdash\>B>>>>>>>>|<row|<cell|<math|<math-ss|cond><rsub|A,B> s
    t\<assign\><math-ss|case><rsub|<value|1>,<value|1>,A,B>
    <around*|(|<math-ss|drop> t|)> <around*|(|<math-ss|drop> s|)>:
    <2>\<times\>A\<vdash\>B>>>>>>
  </with>

  \;

  Thus we can prove that <math|<math-ss|cond>> has the following semantics.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|cond> s
    t|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|cond>
    s t|\<rrbracket\>><around*|\<langle\>|<math-tt|0><rsub|<2>>,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>>>>>
  </eqnarray*>

  With these fundamental operations for Bits in hand, we can define standard
  Boolean connectives.

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|t
    : A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|not><rsub|A>
    t\<assign\><math-ss|cut><rsub|A,<2>\<times\><value|1>,<2>>
    <around*|(|<math-ss|pair> t <math-ss|unit>|)> <around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>: A\<vdash\><2>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\><2>>>|<cell|<math|t
    : A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|and><rsub|A> s
    t\<assign\><math-ss|cut><rsub|A,<2>*\<times\>A,<2>>
    <around*|(|<math-ss|pair> s <math-ss|iden>|)> <around*|(|<math-ss|cond> t
    <math-ss|false>|)>:A\<vdash\><2>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\><2>>>|<cell|<math|t
    : A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|or><rsub|A> s
    t\<assign\><math-ss|cut><rsub|A,<2>*\<times\>A,<2>>
    <around*|(|<math-ss|pair> s <math-ss|iden>|)> <around*|(|<math-ss|cond>
    <math-ss|true> t|)>:A\<vdash\><2>>>>>>>
  </with>

  \;

  We use combinators to define <samp|and> and <samp|or> in order to give them
  short-circut evalutation behaviour. Short-circut evaluation is especially
  useful in our blockchain application because when the second branch does
  not need to be evaluated, the source code for it can be pruned at
  redemption time (see Section<nbsp><with|color|red|TODO>).

  If we had directly define the boolean functions with types
  <math|<math-ss|and-func>:<2>\<times\><2>\<vdash\><2>> and
  <math|<math-ss|or-func>:<2>\<times\><2>\<vdash\><2>>, then the two
  arguments to <samp|and-func> and <samp|or-func> would both need to be fully
  evaluated under strict semantics (see Section<nbsp><with|color|red|TODO>).
  For the <samp|not> combinator, this is less of an issue, but we define it
  in combinator form to be consistent.

  <subsection|Arithmetic>

  In the previous section I was relatively detailed with the annotations
  given to the definitions. Going forward I will be a bit more lax in the
  presentation. We will also start using some notation to abbrevate terms.

  <\eqnarray*>
    <tformat|<table|<row|<cell|s\<times\>t>|<cell|\<assign\>>|<cell|<math-ss|pair>
    s t>>|<row|<cell|s;t>|<cell|\<assign\>>|<cell|<math-ss|comp> s t>>>>
  </eqnarray*>

  with the <math|\<times\>> operator having higher precidence than the
  <math|;> operator.

  Composition of sequences of <samp|drop> and <samp|take> with <samp|ident>
  is a very common way of picking data out of nested tuples of input. To make
  this more concise we will use the following notation.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|H>>|<cell|\<assign\>>|<cell|<math-ss|iden>>>|<row|<cell|<math-ss|O>s<math-ss|>>|<cell|\<assign\>>|<cell|<math-ss|take>
    s>>|<row|<cell|<math-ss|I>s<math-ss|>*>|<cell|\<assign\>>|<cell|<math-ss|drop>
    s>>>>
  </eqnarray*>

  where <math|s> is a string of <samp|I>'s and <samp|O>'s that ends with
  <samp|H>.

  For completely formal definitions of Simplicity expressions, please refer
  to the Coq library.

  By repeatedly taking products of bit types we can build types for
  <math|2<rsup|n>> bit words of any size we want.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<2><rsup|1>>|<cell|\<assign\>>|<cell|<2>>>|<row|<cell|<2><rsup|2>>|<cell|\<assign\>>|<cell|<2><rsup|1>
    \<times\><2><rsup|1>>>|<row|<cell|<2><rsup|4>>|<cell|\<assign\>>|<cell|<2><rsup|2>
    \<times\><2><rsup|2>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|<2><rsup|2<rsup|1+n>>>|<cell|\<assign\>>|<cell|<2><rsup|2<rsup|n>>
    \<times\><2><rsup|2<rsup|n>>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>>>
  </eqnarray*>

  We chose to represent values in big endian format meaning that given a pair
  representing the low and high bits of a value, the most significant bits
  are stored in the first word. Because we are working in the abstract, this
  choice of endianess has no bearing on however a real machine implementation
  chooses to represent the values in memory (see
  Section<nbsp><with|color|red|TODO>).

  Let us recursively define a value function to convert values of these types
  into numbers that they represent.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|1>>|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2n>>|<cell|\<assign\>>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>*2<rsup|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>>>>
  </eqnarray*>

  We will also make use of the following variation of this value conversion
  function.

  <\equation*>
    <around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|n,m>\<assign\><around*|\<lceil\>|a|\<rceil\>><rsub|n>*2<rsup|m>+<around*|\<lceil\>|b|\<rceil\>><rsub|m>
  </equation*>

  These value conversion functions are all injective (one-to-one) and we can
  choose a left inverse. Given <math|m\<of\>\<bbb-N\>>, we implicly define
  <math|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>\<of\><2><rsup|n>> such that
  <math|<around*|\<lceil\>|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>|\<rceil\>><rsub|n>\<equiv\>m
  <around*|(|mod 2<rsup|n>|)>>. We have chosen
  <math|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>> so that it represents
  <math|m> modulo <math|2<rsup|n>>.

  We can equip the type <math|<2><rsup|n>> with addition and multipliction
  operations, so that <math|<around*|\<lfloor\>|\<cdummy\>|\<rfloor\>><rsub|n>>
  becomes a semiring homomorphism. Given <math|a\<of\><2><rsup|n>> and
  <math|b\<of\><2><rsup|n>>, we define <math|a<around*|\<lfloor\>|+|\<rfloor\>><rsub|n>b\<of\><2><rsup|n>>
  and <math|a*<around*|\<lfloor\>|\<times\>|\<rfloor\>><rsub|n>b\<of\><2><rsup|n>>
  such that

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|m<rsub|1>|\<rfloor\>><rsub|n><around*|\<lfloor\>|+|\<rfloor\>><rsub|n><around*|\<lfloor\>|m<rsub|2>|\<rfloor\>><rsub|n>>|<cell|=>|<cell|<around*|\<lfloor\>|m<rsub|1>+m<rsub|2>|\<rfloor\>><rsub|n>>>|<row|<cell|<around*|\<lfloor\>|m<rsub|1>|\<rfloor\>><rsub|n><around*|\<lfloor\>|\<times\>|\<rfloor\>><rsub|n><around*|\<lfloor\>|m<rsub|2>|\<rfloor\>><rsub|n>>|<cell|=>|<cell|<around*|\<lfloor\>|m<rsub|1>*m<rsub|2>|\<rfloor\>><rsub|n>>>>>
  </eqnarray*>

  We will write <math|<math-tt|0><rsub|<2><rsup|4>>,<math-tt|1><rsub|<2><rsup|4>>,\<ldots\>,<math-tt|f><rsub|<2><rsup|4>>>
  to denote the 16 values of <math|<2><rsup|4>> that represent their
  respective hexadecimal values. Similarly we will write
  <math|<math-tt|00><rsub|<2><rsup|8>>,<math-tt|01><rsub|<2><rsup|8>>,\<ldots\>,<math-tt|ff><rsub|<2><rsup|8>>>
  to denote the 256 values of <math|<2><rsup|8>>, and so forth. (It is worth
  observing that for hexadecimal digits <math|<math-tt|<var|x>>> and
  <math|<math-tt|<var|y>>>, we have <math|<math-tt|<var|xy>><rsub|<2><rsup|8>>=<around*|\<langle\>|<math-tt|<var|x>><rsub|<2><rsup|4>>,<math-tt|<var|y>><rsub|<2><rsup|4>>|\<rangle\>>>.)
  While lists of <math|<2><rsup|8>>, known as byte strings, are not a
  Simplicity type, we will at times make use of this type when defining the
  Simplicity langauge. We will write these byte strings as sequences of
  hexadecimal digits, e.g. <math|<math-tt|[53696d706c6963697479]><rsub|<2><rsup|8>>>.
  For all these values, we may omit the subscript when the interpretation is
  clear from the context.

  Using techniques familiar from digitial logic we can build an adders and
  full adders from our Boolean operations defined in the previous section. We
  begin with definitions of the single bit adder and full adder.

  <\render-code>
    <math|<math-ss|adder><rsub|1> :<2>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|cond>
    <around*|(|<math-ss|iden>\<times\><math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false>\<times\><math-ss|iden>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-adder><rsub|1> :<around*|(|<2>\<times\><2>|)>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <math-ss|adder><rsub|1>\<times\> <math-ss|IH>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|OOH>\<times\><around*|(|<math-ss|OIH>\<times\>
    <math-ss|IH> ;<math-ss|adder><rsub|1>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|<math|<math-ss|cond>
    <math-ss|true> <math-ss|OH>\<times\><math-ss|IIH>>>>>>>>>>>>>>
  </render-code>

  These two adders meet the following specification.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  It is easy to exhaustively check the above equations because there are only
  a small finite number of possible inputs to consider (four inputs for
  <math|<math-ss|adder><rsub|1>> and eight inputs for
  <math|<math-ss|full-adder><rsub|1>>). We will illustrate this for a single
  case for <math|<math-ss|adder><rsub|1>> where
  <math|a=<math-tt|1><rsub|<2>>> and <math|b=<math-tt|0><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|cond>
    <around*|(|<math-ss|iden>\<times\><math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false>\<times\><math-ss|iden>|)>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|iden>\<times\><math-ss|not>
    <math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|not>
    <math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>; <around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|unit>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,1<rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>\<cdot\>2<rsup|1>+<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|0\<cdot\>2+1>>|<row|<cell|>|<cell|=>|<cell|1>>|<row|<cell|>|<cell|=>|<cell|1+0>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>+<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  The calculations for the other cases are similar.

  <math|>

  Next we recursively build adders and full adders for any word size.

  <\render-code>
    <math|<math-ss|full-adder><rsub|2n> :<around*|(|<2><rsup|2n>\<times\><2><rsup|2n>|)>\<times\><2>\<vdash\><2>\<times\><2><rsup|2n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|2n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>\<times\><around*|(|<math-ss|take>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IIH>|)>\<times\> <math-ss|IH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|adder><rsub|2n> :<math|<2><rsup|2n>>\<times\><math|<2><rsup|2n>>\<vdash\><2>\<times\><math|<2><rsup|2n>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|2n>>>|<cell|:=>|<cell|<math|<around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>\<times\><around*|(|<math-ss|OIH>\<times\><math-ss|IIH>
    ;<math-ss|adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  We generalize the specification for the single bit adders and full adders
  to the multi-bit adders and full adders.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  <\theorem>
    For all <math|n> which is a power of 2, and for all <math|a:<2><rsup|n>>,
    <math|b :<2><rsup|n>>, and <math|c :<2>>, we have that
    <math|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>.
  </theorem>

  <\proof>
    We prove <math|<math-ss|full-adder><rsub|n>> meets its specification by
    induction on <math|n>. As mentioned before,
    <math|<math-ss|full-adder><rsub|1>> case is easily checked by verifying
    all eight possible inputs. Next we prove that
    <math|<math-ss|full-adder><rsub|2n>> meets its specification under the
    assumption that <math|<math-ss|full-adder><rsub|n>> does. Specifically we
    want to show that

    \;

    <\equation>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,2*n>=<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1><label|full-adder-spec>
    </equation>

    Let us first consider the right hand side of equation
    <reference|full-adder-spec>. By the definition of our value function we
    have that\ 

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
    </eqnarray*>

    By our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>
    </equation*>

    so we know that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>
    </equation*>

    Let us define <math|c<rsub|0>> and <math|r<rsub|2>> such that
    <math|<around*|\<langle\>|c<rsub|0>,r<rsub|2>|\<rangle\>>\<assign\>><math|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<langle\>|c<rsub|0>,r<rsub|2>|\<rangle\>>|\<rceil\>><rsub|1,n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>>>>>
    </eqnarray*>

    Again, by our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>
    </equation*>

    therefore we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>
    </equation*>

    Let us define <math|c<rsub|1>> and <math|r<rsub|1>> such that
    <math|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>\<assign\>><math|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n><eq-number><label|full-adder-RHS>>>>>
    </eqnarray*>

    Now let us consider the left hand side of equation
    <reference|full-adder-spec>. By the definition and semantics of
    <math|<math-ss|full-adder><rsub|2n>> we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
      ;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|take>
      <around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>\<times\><around*|(|<math-ss|take>
      <around*|(|<math-ss|OIH>\<times\><math-ss|IIH>|)>\<times\> <math-ss|IH>
      ;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
      ;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
      ;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|c<rsub|0>,r<rsub|2>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|2>,<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|2>,<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|2>|\<rangle\>>|\<rangle\>>>>>>
    </eqnarray*>

    Therefore we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,2*n>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|2>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|<around*|\<langle\>|r<rsub|1>,r<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|*n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n><eq-number><label|full-adder-LHS>>>>>
    </eqnarray*>

    Together equations <math|><reference|full-adder-RHS> and
    <reference|full-adder-LHS> show that the right hand side and left hand
    side of equation <reference|full-adder-spec> are equal, as required.
  </proof>

  The proof that <math|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>
  is done in a similar manner. Computered verified versions of theses proofs
  can be found in the Coq library (see Section<nbsp><with|color|red|TODO>).

  With a full adder we can recursively build multipliers and full multiplier
  in a similar way.

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|1>
    :<around*|(|<2>\<times\><2>|)>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|IH>\<times\><math-ss|take>
    <around*|(|<math-ss|cond> <math-ss|iden> <math-ss|false>|)>
    ;<math-ss|full-adder><rsub|1>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|2n>
    :<around*|(|<math|<2><rsup|2n>>\<times\><2><rsup|2n>|)>\<times\><around*|(|<math|<2><rsup|2n>>\<times\><math|<2><rsup|2n>>|)>\<vdash\><2><rsup|4n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiplier><rsub|2n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH>\<times\><around*|(|<math-ss|IOH>\<times\><math-ss|OIH>|)>|)>>>>|<row|<cell|>|<cell|<math|\<times\>>>|<cell|(<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IIH>|)>\<times\><math-ss|drop>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>>>>|<row|<cell|>|<cell|<math|\<times\>>>|<cell|<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IIH>|)>\<times\><math-ss|drop>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>>)>>|<row|<cell|>|<cell|<math|;>>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OH>\<times\><math-ss|IOH>|)>>>>|<row|<cell|>|<cell|<math|\<times\>>>|<cell|<math|<around*|(|<math-ss|drop>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IIH>|)>\<times\><around*|(|<math-ss|OIH>\<times\><math-ss|drop>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>|)>>>>|<row|<cell|>|<cell|<math|;>>|<cell|<math|<around*|(|<math-ss|OH>\<times\><math-ss|drop>
    <around*|(|<math-ss|IOH>\<times\><math-ss|OOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>\<times\><math-ss|drop>
    <around*|(|<math-ss|IIH>\<times\><math-ss|OIH>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|multiplier><rsub|1> :<2>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|false>\<times\><math-ss|cond>
    <math-ss|iden> ><samp|false>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|multiplier><rsub|2n> :<math|<2><rsup|2n>>\<times\><2><rsup|2n>\<vdash\><2><rsup|4n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|3|5|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|multiplier><rsub|2n>>>|<cell|:=>|<cell|<math|
    <around*|(|<math-ss|OOH>\<times\><around*|(|<math-ss|IOH>\<times\><math-ss|OIH>|)>|)>>>>|<row|<cell|>|<cell|<math|\<times\>>>|<cell|<math|<around*|(|<math-ss|><around*|(|<math-ss|OOH>\<times\><math-ss|IIH>|)>
    ;<math-ss|multiplier><rsub|n>|)>\<times\><around*|(|<around*|(|<math-ss|OIH>\<times\><math-ss|IIH>|)>
    ;<math-ss|multiplier><rsub|n>|)>>>>|<row|<cell|>|<cell|<math|;>>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OH>\<times\><math-ss|IOH>|)>>>>|<row|<cell|>|<cell|<math|\<times\>>>|<cell|<math|<around*|(|<math-ss|drop>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IIH>|)>\<times\><around*|(|<math-ss|OIH>\<times\><math-ss|drop>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>|)>>>>|<row|<cell|>|<cell|<math|;>>|<cell|<math|<around*|(|<math-ss|OH>\<times\><math-ss|drop>
    <around*|(|<math-ss|IOH>\<times\><math-ss|OOH>|)>
    ;<math-ss|full-multiplier><rsub|n>|)>\<times\><math-ss|drop>
    <around*|(|<math-ss|IIH>\<times\><math-ss|OIH>|)>>>>>>>>>>>>
  </render-code>

  We can prove that the multipliers and full multipliers meet the following
  specifications.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,<around*|\<langle\>|c,d|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2*n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\><around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|n>+<around*|\<lceil\>|d|\<rceil\>><rsub|n>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\><around*|\<lceil\>|b|\<rceil\>><rsub|n>>>>>
  </eqnarray*>

  \;

  <with|color|red|TODO: notes on tradeoffs between efficency and simplicity.>

  <subsection|Bitwise Operations>

  <subsection|SHA-256>

  The offical standard for the SHA-2 family, which includes SHA-256 can be
  found in the <hlink|FIPS PUB 180-4: Secure Hash Standard
  (SHS)|http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>. We define
  the SHA-256 function, <math|SHA256<rsub|<2>>\<of\><2><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>,
  as a function from bit strings to a 256-bit word. Technically, the SHA-256
  is restricted to inputs <math|l\<of\><2><rsup|\<ast\>>> whose bit length is
  restricted such that <math|<around*|\||l|\|>\<less\>2<rsup|64>>.

  The SHA-256 hash function is composed out of two components, a padding
  function <math|SHA256<rsub|Pad>\<of\><2><rsup|\<ast\>>\<rightarrow\><around*|(|<2><rsup|512>|)><rsup|+>>,
  which appends padding and length data to produce a (non-empty) sequence of
  blocks of 512 bits, and the Merkle--Damgård construction
  <math|SHA256<rsub|MD>\<of\><2><rsup|256>\<rightarrow\><around*|(|<2><rsup|512>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\equation*>
    SHA256<rsub|<2>>=SHA256<rsub|MD><around*|(|SHA256<rsub|IV>|)>\<circ\>\<eta\><rsup|S>\<circ\>SHA256<rsub|Pad>
  </equation*>

  where <math|SHA256<rsub|IV>\<of\><2><rsup|256>> is the SHA-256 initial
  value and <math|\<eta\><rsup|S><rsub|A<rsup|+>>\<of\>A<rsup|+>\<rightarrow\>A<rsup|\<ast\>>>
  formally converts a non-empty list to a regular list.

  The <math|SHA256<rsub|MD>> is a left fold using the SHA-256 block
  compression function <math|SHA256<rsub|Block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<rightarrow\><2><rsup|256>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|SHA256<rsub|MD><around*|(|h|)><around*|(|\<epsilon\>|)>>|<cell|\<assign\>>|<cell|h>>|<row|<cell|SHA256<rsub|MD><around*|(|h|)><around*|\<langle\>|b\<blacktriangleleft\>l|\<rangle\>>>|<cell|\<assign\>>|<cell|SHA256<rsub|MD><around*|(|SHA256<rsub|Block><around*|\<langle\>|h,b|\<rangle\>>|)><around*|(|l|)>>>>>
  </eqnarray*>

  The block compression function <math|SHA256<rsub|Block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<rightarrow\><2><rsup|256>>
  is a function that has a type that fits in Simplicity's framework. We can
  create a core Simplicity term <math|<math-ss|sha256-block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<vdash\><2><rsup|256>>
  that implements this function

  <\equation*>
    <around*|\<llbracket\>|<math-ss|sha256-block>|\<rrbracket\>>=SHA256<rsub|Block>
  </equation*>

  We can also define SHA-256's initial value
  <math|<math-ss|sha256-iv>\<of\><value|1>\<vdash\><2><rsup|256>>.

  <\equation*>
    <around*|\<llbracket\>|<math-ss|sha256-iv>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>=SHA256<rsub|IV>
  </equation*>

  Beyond defining the block compression function in the Simplicity language,
  we will also be using the SHA-256 hash function elsewhere in this
  specification. In practice, SHA-256 is applied to byte strings rather than
  bit strings. To this end we define the variant
  <math|SHA256<rsub|<2><rsup|8>>\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\equation*>
    SHA256<rsub|<2><rsup|8>>\<assign\>SHA256<rsub|<2>>\<circ\>\<mu\><rsup|\<ast\>>\<circ\><around*|(|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>|)><rsup|\<ast\>>
  </equation*>

  where <math|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>\<of\><2><rsup|8>\<rightarrow\><2><rsup|\<ast\>>>
  formally converts a byte to a bit string (in big endian format).

  <\equation*>
    \<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|b<rsub|2>,<rsub|>b<rsub|3>|\<rangle\>>|\<rangle\>>,<around*|\<langle\>|<around*|\<langle\>|b<rsub|4>,b<rsub|5>|\<rangle\>>,<around*|\<langle\>|b<rsub|6>,b<rsub|7>|\<rangle\>>|\<rangle\>>|\<rangle\>>\<assign\>b<rsub|0>\<blacktriangleleft\>b<rsub|1>\<blacktriangleleft\>b<rsub|2>\<blacktriangleleft\>b<rsub|3>\<blacktriangleleft\>b<rsub|4>\<blacktriangleleft\>b<rsub|5>\<blacktriangleleft\>b<rsub|6>\<blacktriangleleft\>b<rsub|7>\<blacktriangleleft\>\<epsilon\>
  </equation*>

  Since the <math|SHA256<rsub|<2><rsup|8>>> variant is so commonly used, we
  will write it unaddorned as simply <math|SHA256>.

  <subsection|Modular Arithmetic>

  <subsection|Elliptic Curve Operations>

  <section|Completeness Theorem>

  General purpose programming languages are famously incomplete because there
  are functions that are uncomputable, the halting problem being the most
  famous of these. Core Simplicity is even more limited that these general
  purpose programming languages because the denotational semantics are
  limited to functions from finite types to finite types.

  However, we can ask the question, is every function from a finite type to a
  finite type expressible in Core Simplicity? This question is answered by
  the completeness theorem as yes.

  <\theorem>
    <label|thm:CSCT>Core Simplicity Completeness Theorem. For any
    (Simplicity) types <math|A> and <math|B> and any function
    <math|f:A\<rightarrow\>B>, there exists some Core Simplicity term
    <math|t> such that for all <math|a:A>,

    <\equation*>
      <around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>=f<around*|(|a|)>
    </equation*>
  </theorem>

  This result is possible because these functions are all finitary and can
  be, in principle, expressed as a large lookup table. It is possible to
  encode these lookup tables as Simplicity expressions. The formal proof of
  this theorem can be found in the Coq library (see
  Section<nbsp><with|color|red|TODO>).

  It is worth emphasizing that this result is a purely theoretical result
  that show that Core Simplicity is fully expressive for it's domain; it is
  completely impractical to generate Simplicity expressions this way as many
  expressions would be astronomical in size. Thus we can see Simplicity
  programming as an exercise in compression: how can we take advantage of the
  structure within computations to expression our required functions
  succinctly to avoid expressing functions as a large lookup table.

  <section|Operational Semantics>

  The denotational semantics of Simplicity determine the functional behaviour
  of expressions. However, they are not suitable for determining the
  computation resources needed to evaluate expressions. For this reason we
  define an operational semantics for Simplicity via an abstract machine we
  call the <dfn|Bit Machine>.

  <subsection|Repesenting Values as Cell Arrays><label|ss:RepresentingValuesAsCellArrays>

  <assign|carr|<macro|x|<verbatim|[<arg|x>]>>><assign|cearr|<macro|x|<verbatim|[<arg|x><underline|]>>>><assign|rep|<macro|x|y|<math|\<ulcorner\><arg|x>\<urcorner\><rsub|<arg|y>>>>>Values
  in the Bit Machine are represented by arrays of cells where each cell
  contains one of three values: a <verbatim|0> value, a <verbatim|1> value,
  or a <verbatim|?> value which we call an undefined value. We write an array
  of cell by enclosing a sequence of cells with square brackets (e.g.
  <carr|1?0>). We denote the length of an array using
  <math|<around*|\||\<cdummy\>|\|>>. For example,
  <math|<around*|\||<carr|1?0>|\|>=3>. The concatenation of two arrays,
  <math|a> and <math|b> is denoted by <math|a\<cdot\>b>, and replication of
  an array <math|n> times is denoted by expontiation, <math|a<rsup|n>>.
  Sometimes we will omit the dot whed performing concatenation.

  For any given type, we define the number of cells needed to hold values of
  that type using the following <math|bitSize> function.

  <\eqnarray*>
    <tformat|<table|<row|<cell|bitSize<around*|(|<value|1>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|bitSize<around*|(|A+B|)>>|<cell|\<assign\>>|<cell|1+max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>>>|<row|<cell|bitSize<around*|(|A\<times\>B|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>+bitSize<around*|(|B|)>>>>>
  </eqnarray*>

  We define a represenation of values of Simplicity types as arrays of cells
  as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<around*|\<langle\>||\<rangle\>>|<value|1>>>|<cell|\<assign\>>|<cell|<carr|>>>|<row|<cell|<rep|<injl-long|A|B|<around*|(|a|)>>|A+B>>|<cell|\<assign\>>|<cell|<carr|0>\<cdot\><carr|?><rsup|padL<around*|(|A,B|)>>\<cdot\><rep|a|A>>>|<row|<cell|<rep|<injr-long|A|B|<around*|(|b|)>>|A+B>>|<cell|\<assign\>>|<cell|<carr|1>\<cdot\><carr|?><rsup|padR<around*|(|A,B|)>>\<cdot\><rep|b|B>>>|<row|<cell|<rep|<around*|\<langle\>|a,b|\<rangle\>>|A\<times\>B>>|<cell|\<assign\>>|<cell|<rep|a|A>\<cdot\><rep|b|B>>>>>
  </eqnarray*>

  The representation of values of a sum type are padded with undefined cells
  so that the representation has the proper length.

  <\eqnarray*>
    <tformat|<table|<row|<cell|padL<around*|(|A,B|)>>|<cell|\<assign\>>|<cell|max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>-bitSize<around*|(|A|)>>>|<row|<cell|padR<around*|(|A,B|)>>|<cell|\<assign\>>|<cell|max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>-bitSize<around*|(|B|)>>>>>
  </eqnarray*>

  <\theorem>
    Given any value of some Simplicity type, <math|a:A>, we have
    <math|<around*|\||<rep|a|A>|\|>=bitSize<around*|(|A|)>>.
  </theorem>

  <subsection|Bit Machine>

  A frame is a, possibly empty, cell array with a cursor referencing a cell
  in the array, which we denote using an underscore.

  <\equation*>
    <carr|0<underline|1>?10>
  </equation*>

  The cursor may also reference the end of the array, which we denote by
  marking the end of the array with an underscore.

  <\equation*>
    <cearr|01?10>
  </equation*>

  Frames can be concatenated with cell arrays either on the left or on the
  right without moving the cursor. Note that when concatenating a non-empty
  cell array onto the right hand side of a frame whose cursor is at the end
  of the frame, the cursor ends up pointing to the first cell of the added
  cell array.

  <\equation*>
    <cearr|01?10><carr|111??>=<carr|01?10<wide*|1|\<bar\>>11??>
  </equation*>

  <assign|emptyFrame|<math|<tiny|\<wedge\>>>>We will sometimes denote the
  empty frame, <math|<cearr|>>, with a small cursor, <value|emptyFrame>.

  The state of the Bit Machine consistes of two non-empty stacks of frames: a
  read-frame stack and a write-frame stack. The top elements of the two
  stacks are called the <dfn|active read frame> and the <dfn|active write
  frame> respectively. The other frames are called inactive read-frames or
  inactive write-frames.

  <big-figure|<tabular|<tformat|<cwith|1|1|1|-1|cell-tborder|2px>|<cwith|5|5|1|-1|cell-bborder|2px>|<cwith|1|1|1|-1|cell-bborder|1px>|<table|<row|<cell|read
  frame stack>|<cell|write frame stack>>|<row|<cell|<carr|100<underline|1>1??110101000>>|<cell|<cearr|11??1101>>>|<row|<cell|<carr|<underline|0>000>>|<cell|<carr|111<underline|?>?>>>|<row|<cell|<cearr|>>|<cell|>>|<row|<cell|<carr|<underline|1>0>>|<cell|>>>>>|Example
  state of the Bit Machine.>

  <assign|halted|<math|<op|\<boxtimes\>>>>Notationally we will write a stack
  of read frames as <math|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>>,
  with <math|r<rsub|0>> as the active read frame. We will write a stack of
  write frames in the opposite order, as <math|w<rsub|0>\<vartriangleleft\>w<rsub|1>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>>
  with <math|w<rsub|0><rsub|>> as the active write frame. We write a state of
  the Bit Machine as <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>
  where <math|\<Theta\>> is the (possibly empty) inactive read frame stack,
  <math|\<Xi\>> is the (possibly empty) inactive write frame stack,
  <math|r<rsub|0>> is the active read frame, and <math|w<rsub|0>> is the
  active write frame.<\footnote>
    The notation for the Bit Machine's state is intended to mimic the gap
    buffer used in our C implemenation of the Bit Machine (see
    <with|color|red|TODO>).
  </footnote> There is one additional state of the Bit Machine called the
  <dfn|halted> state, which we denote by <value|halted>.

  The Bit Machine has nine basic instructions that, when executed, transform
  the Bit Machine's state. We denote these basic instructions as
  <math|i:S<rsub|0>\<rightsquigarrow\>S<rsub|1>>, where <math|i> is the
  instructions's name, <math|S<rsub|0>> is a state of the Bit Machine before
  executing the instruction, and <math|S<rsub|1>> is the state of the machine
  after the successful execution of the instructions.

  <subsubsection|Frame Instructions>

  Our first three basic instructions, create, move, and delete active frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|newFrame<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
    \<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|<emptyFrame><carr|?><rsup|n>\<vartriangleleft\>w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|moveFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0><emptyFrame>\<vartriangleleft\>w<rsub|1>\<vartriangleleft\>\<Xi\>|]>
    \<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<vartriangleright\><emptyFrame>w<rsub|0>\|w<rsub|1>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|dropFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>\|\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|\<Xi\>|]>>>>>
  </eqnarray*>

  Executing a <math|newFrame<around*|(|n|)>> instruction pushes a new frame
  of length <math|n> onto the write frame stack. This new frame has its
  cursor at the beginning of the frame and the entire frame is filled with
  undefined values. It is legal for the new frame to have length 0.

  Executing the <math|moveFrame> instruction moves the top frame of the write
  frame stack to the read frame stack. This instruction is only legal to
  execute when the cursor of the active write frame is at the end of the
  frame. The cursor is reset to the beginning of the frame when it is placed
  onto the read frame stack.

  Executing the <math|dropFrame> instructions removes the top frame of the
  read frame stack.

  <subsubsection|Active Write Frame Instructions>

  Our next three instructions are used to write data to the active write
  frame.

  <\eqnarray*>
    <tformat|<table|<row|<cell|write<around*|(|0|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|<wide*|?|\<bar\>>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><cearr|0><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|write<around*|(|1|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|<wide*|?|\<bar\>>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><cearr|1><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|skip<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0><emptyFrame><carr|?><rsup|n+m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|?><rsup|n><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|copy<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|n+m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><cearr|c<rsub|1>\<cdots\>c<rsub|n>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>>>
  </eqnarray*>

  Executing a <math|write<around*|(|b|)>> instruction writes a 0 or 1 to the
  active write frame and advances its cursor. Writing an undefined value
  using this instruction is not allowed. The cursor cannot be at the end of
  the frame.

  Executing a <math|skip<around*|(|n|)>> instruction advances the active
  write frame's cursor without writing any data. There must be sufficent
  number of cells after the cursor. The trivial instruction
  <math|skip<around*|(|0|)>> is legal and executing it is effectively a nop.

  Executing a <math|copy<around*|(|n|)>> instruction copies the values of the
  <math|n> cells after the active read frame's cursor into the active write
  frame, advancing the write frame's cursor. The must be a sufficent number
  of cells after both the active read frame and active write frame's cursors.
  Note that undefined cell values are legal to copy. The trivial instruction
  <math|copy<around*|(|0|)>> is legal and executing it is effectively a nop.

  <subsubsection|Active Read Frame Instructions>

  The next two instructions are used to manipulate the active read frame's
  cursor.

  <\equation*>
    fwd<around*|(|n|)>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  <\equation*>
    bwd<around*|(|n|)>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  Executing a <math|fwd<around*|(|n|)>> instructions moves the cursor on the
  active read frame forward, and executing a <math|bwd<around*|(|n|)>>
  instruction moves the cursor backwards. In both cases there must be
  sufficent number of cells before or after the cursor. The trivial
  instructions <math|fwd<around*|(|0|)>> and <math|bwd<around*|(|0|)>> are
  legal and executing them are effectively nops.

  <subsubsection|Abort Instruction>

  The final instruction of for the Bit Machine moves from any non-halted
  state into the halted state.

  <\equation*>
    abort:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><halted>
  </equation*>

  This is the only way to enter the halted state, and once in the halted
  state no further insturctions can be executed.

  <subsubsection|Bit Machine Programs>

  <assign|prog|<macro|x|p|y|<math|<arg|x><math-relation|\<#291C\>><arg|p>\<twoheadrightarrow\><arg|y>>>>The
  basic instructions of the Bit Machine are combined to produce programs that
  take the Bit Machine through a sequence of states. We write
  <prog|S<rsub|0>|k|S<rsub|1>> for a program, <math|k>, that, when executed,
  successfully transfroms an initial state <math|S<rsub|0>> to the final
  state <math|S<rsub|1>>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<prog|S|nop|S>>>>>>
  </with>

  We write <math|nop> for the trival program with no instructions. The inital
  and final states are identical in this case.

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:S<rsub|0>\<rightsquigarrow\>S<rsub|1>>>>|<row|<cell|<prog|S<rsub|0>|i|S<rsub|1>>>>>>>
  </with>

  For every basic instruction there is a single instruction program whose
  intial and final states match those of the basic instruction.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>>|<cell|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>>>>>>>>|<row|<cell|<prog|S<rsub|0>|k<rsub|0>;k<rsub|1>|S<rsub|2>>>>>>>
  </with>

  \;

  We write <math|k<rsub|0>;k<rsub|1>> for a sequence of two programs,
  <math|k<rsub|0>> and <math|k<rsub|1>>. The Bit Machine executes the two
  programs in turn, concatenating the sequence of states of the two programs.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S<rsub|>>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>k<rsub|1>|S>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>k<rsub|1>|S>>>>>>
  </with>

  We define <math|k<rsub|0><around*|\|||\|>k<rsub|1>> as a deterministic
  choice between two programs, <math|k<rsub|0>> and <math|k<rsub|1>>. When
  executing a determinsitc choice, the value under the active read frame's
  cursor decides which one of the two programs are executed. When
  encountering a determinisitc choice, the active read frame's cursor must
  not be at the end of its array and the cell under the cursor must not be an
  undefined value.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<halted>|k|<halted>>>>>>>
  </with>

  Lastly, we stipulate that every program when executed from the halted state
  ignores all instructions and perfrom a nop instead.

  Take care to note this difference between instructions and programs
  containing one instruction. A single instruction cannot be executed
  starting from the halted state, while a program that consists of a single
  instruction can be run starting from the halted state (however, it does
  nothing from this state).

  <\equation*>
    n\<star\>k\<assign\>fwd<around*|(|n|)>;k;bwd<around*|(|n|)>
  </equation*>

  The <math|n\<star\>k> notation (called ``bump'') is for a program that
  temporarily advances the active read frame's cursor when executing
  <math|k>.

  <\theorem>
    \;

    <\with|par-mode|center>
      <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|n\<star\>k|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>>>>
    </with>

    \;
  </theorem>

  <subsubsection|Crashing the Bit Machine>

  Bit Machine programs are deterministic. Given a program <math|k> and an
  initial state <math|S<rsub|0>> there exists at most one state
  <math|S<rsub|1>> such that <prog|S<rsub|0>|k|S<rsub|1>>. However it is
  possible that there is no state <math|S<rsub|1>> such that
  <prog|S<rsub|0>|k|S<rsub|1>> given an initial state for a program. This
  happens when the Bit Machine is trying to execute a single instruction
  program, <math|i>, from a non-halted state where that instruction cannot
  legally execute from. This can also happen when a determinstic choice
  operation is encounted starting from a state where the active read frame's
  cursor is at the end of the frame, or is referencing and undefined value.

  When a program cannot execute to completion from a given inital state, we
  say that the Bit Machine crashes, or we say that the program crashes the
  Bit Machine. Crashing is distinct from halting. We will have a number of
  theorems that prove that a Bit Machine interpreting a Simpicity expression
  from a suitable initial state never crashes the Bit Machine; however in
  some of these cases the program may cause the Bit Machine to legitmately
  enter the halted state.

  <subsection|Executing Simplicity>

  We recursively translate a Core Simplicity program, <math|t \<of\> A
  \<vdash\>B>, into a program for the Bit Machine,
  <math|<around*|\<llangle\>|t|\<rrangle\>>>, called the naive translation:

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llangle\>|<math-ss|iden><rsub|A>|\<rrangle\>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|<around*|\<llangle\>|<math-ss|comp><rsub|A,B,C>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<around*|\<llangle\>|s|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|<around*|\<llangle\>|<math-ss|unit><rsub|A>|\<rrangle\>>>|<cell|\<assign\>>|<cell|nop>>|<row|<cell|<around*|\<llangle\>|<math-ss|injl><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|A,B|)>|)>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|injr><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|A,B|)>|)>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|(|1+padL<around*|(|A,B|)>|)>\<star\><around*|\<llangle\>|s|\<rrangle\>>>>|<row|<cell|>|<cell|<around*|\|||\|>>|<cell|<around*|(|1+padR<around*|(|A,B|)>|)>\<star\><around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|pair><rsub|A,B,C>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llangle\>|s|\<rrangle\>>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|take><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|drop><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>\<star\><around*|\<llangle\>|t|\<rrangle\>>>>>>
  </eqnarray*>

  <\theorem>
    Given a well-typed core Simplicity program <math|t:A\<vdash\>B> and an
    input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any stacks <math|><math|\<Theta\>>, <math|\<Xi\>>, and
    any natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have\ 

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  which means we if we start the Bit Machine with only the input represented
  on the read stack, and enough space for the output on the write stack, the
  Bit Machine will compute the representation of the value
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>> without
  crashing.

  <subsubsection|Tail Composition Optimisation (TCO)>

  <assign|TCOon|<macro|x|<math|<around*|\<llangle\>|<arg|x>|\<rrangle\>><rsup|TCO><rsub|on>>>><assign|TCOoff|<macro|x|<math|<around*|\<llangle\>|<arg|x>|\<rrangle\>><rsup|TCO><rsub|off>>>>Traditional
  imperative language implementations often make use of tail call
  optimization that occurs when the last command of a procedure is a call to
  a second procedure. Normally the first procedure's stack frame would be
  free after the second procedure returns. The tail call optimization instead
  frees the first procedure's stack frame prior to the call to the second
  procedure instead. This can reduce the overall memory use of the program.

  The composition combinator, <math|<math-ss|comp>>, in Simplicity plays a
  role similar to a procedure call. We can perform a tail composition
  optimization that moves the <math|dropFrame> instruction earlier to reduce
  the overall memory requirements needed to evaluate Simplicity programs. We
  define an alternate translation of Simplicity programs to Bit Machine
  programs via two mutually recursively defined functions,
  <math|<TCOoff|\<cdummy\>>> and <TCOon|\<cdummy\>>:

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|15|28|2|2|cell-halign|r>|<table|<row|<cell|<TCOoff|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|<TCOoff|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOoff|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<TCOon|t>>>|<row|<cell|<TCOoff|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|nop>>|<row|<cell|<TCOoff|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|A,B|)>|)>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|A,B|)>|)>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|<around*|(|1+padL<around*|(|A,B|)>|)>\<star\><TCOoff|s>>>|<row|<cell|>|<cell|<around*|\|||\|>>|<cell|<around*|(|1+padR<around*|(|A,B|)>|)>\<star\><TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|<TCOoff|s>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>\<star\><TCOoff|t>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<TCOon|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|<TCOon|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOon|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|dropFrame>>|<row|<cell|<TCOon|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|A,B|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|A,B|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|fwd<around*|(|1+padL<around*|(|A,B|)>|)>;<TCOon|s>>>|<row|<cell|>|<cell|<around*|\|||\|>>|<cell|fwd<around*|(|1+padR<around*|(|A,B|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|<TCOoff|s>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|fwd<around*|(|bitSize<around*|(|A|)>|)>;<TCOon|t>>>>>
  </eqnarray*>

  The definition of the <math|<TCOoff|\<cdummy\>>> translation is very
  similar to the naive one, except the dropFrame instruction at the end of
  the translation of the composition combinator is replaced by having a
  recursive call to <math|<TCOon|\<cdummy\>>> instead. The definition of
  <math|<TCOon|\<cdummy\>>> puts the dropFrame instruction in the
  translations of <math|<math-ss|iden>> and <math|<math-ss|unit>>. The
  <math|bwd> instructions are removed from the translations of
  <math|<math-ss|case>> and <math|<math-ss|drop>>. Lastly notice that the
  first recursive call in the translation of <math|<math-ss|pair>> is to
  <TCOoff|\<cdummy\>>.

  <\theorem>
    Given a well-typed core Simplicity program <math|t:A\<vdash\>B> and an
    input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOoff|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOon|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any frame <math|r<rsub|1>>, any stacks
    <math|><math|\<Theta\>>, <math|\<Xi\>>, and any natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have\ 

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  <section|Static Analysis>

  Static analysis lets us quickly compute properties of programs, without the
  need for exhasutively executing programs on all possible inputs. We use
  static analysis in Simplicity to bound the computation costs in terms of
  time and space of Simplicity programs for all their inputs. The analysis we
  do are linear in the size of the DAG representing the Simplicity
  expression, and typically the analysis runs much faster than the cost of
  even evaluating an expression on a single input. We can do this because the
  intermediate results of static analysis can be shared where there are
  shared sub-expressions.

  <subsection|Space Resources>

  The primary source of memory resources used by the Bit Machine is the cells
  used by all the frames that make of the state of Bit Machine. A secondary
  source of memory resources used comes from the overhead of the frames
  themselves, which need to store their bounderies or sizes, and the position
  of their cursors. In our analysis we will make a simplifying assumption
  that these bounderies / sizes / positions values are all of constant size.
  This assumption holds when the Bit Machine is implemented on real hardware
  which has an upper bound on its addressable memory and there is a limit on
  the number of Cells that can be held anyways.

  To bound these resources we perform a static analysis to compute an upper
  bound on the maximum number of cells needed when executing a Simplicity
  program on the Bit Machine for any input, and we compute an upper bound on
  the maximum number of frames needed as well.

  <subsubsection|Maximum Cell Count Bound>

  We define the cell count of a frame to be the length of its underlying cell
  array and the cell count of a Bit Machine state to be the sum of the cell
  counts of all its frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|cellCount<around*|(|<carr|c<rsub|1>\<cdots\><wide*|c<rsub|i>|\<bar\>>\<cdots\>c<rsub|n>>|)>>|<cell|\<assign\>>|<cell|n>>|<row|<cell|cellCount<around*|(|<around*|[|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>|]>|)>>|<cell|\<assign\>>|<cell|<big|sum><rsup|n><rsub|i=0>cellCount<around*|(|r<rsub|i>|)>+<big|sum><rsup|m><rsub|j=0>cellCount<around*|(|w<rsub|j>|)>>>|<row|<cell|cellCount<around*|(|<halted>|)>>|<cell|\<assign\>>|<cell|0>>>>
  </eqnarray*>

  We define the cells required by a program <prog|S<rsub|0>|p|S<rsub|1>> as
  the maximum cell count over every intermediate state.

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<math|cellsReq<around*|(|<prog|S<rsub|>|nop|S<rsub|>>|)><rsub|>\<assign\>
    cellCount<around*|(|S<rsub|>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:S<rsub|0>\<rightsquigarrow\>S<rsub|1>>>>|<row|<cell|<math|cellsReq<around*|(|<prog|S<rsub|0>|i|S<rsub|1>>|)><rsub|>\<assign\>
    max<around*|(|cellCount<around*|(|S<rsub|0>|)>,cellCount<around*|(|S<rsub|1>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>>|<cell|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>>>>>>>>|<row|<cell|<math|cellsReq<around*|(|<prog|S<rsub|0>|k<rsub|0>;k<rsub|1>|S<rsub|2>>|)>\<assign\>max<around*|(|cellsReq<around*|(|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>|)>,cellsReq<around*|(|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S>>>|<row|<cell|<math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>k<rsub|1>|S>|)><rsub|>\<assign\>cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>>>|<row|<cell|<math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>k<rsub|1>|S>|)><rsub|>\<assign\>cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<math|cellsReq<around*|(|<prog|<halted>|k|<halted>>|)><rsub|>\<assign\>
    0>>>>>>
  </with>

  \;

  Note that when executing a Simplicity expression on the Bit Machine, the
  size of the state prior and after execution is identical. For naive
  transation of Simplicity to the Bit Machine, we can write a simple
  recursive function that bounds the number of additional Cells needed to
  evaluate a Simplicity expression beyond the size of the inital and final
  state.

  <\eqnarray*>
    <tformat|<cwith|2|10|2|2|cell-halign|r>|<cwith|2|10|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<around*|(|<math-ss|iden><rsub|A>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|B|)>+max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|unit><rsub|A>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<around*|(|<math-ss|injl><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|injr><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|take><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|drop><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>>>
  </eqnarray*>

  <\lemma>
    For any core Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>+extraCellsBound<around*|(|t|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<around*|(|t|)>>.
  </lemma>

  We can compute a tighter bound for TCO translation, but the calculation is
  a bit more complicated. The number of extra cells needed depends on whether
  TCO is in the ``on'' state, and what the size of the active read frame is.

  <\eqnarray*>
    <tformat|<cwith|2|10|2|2|cell-halign|r>|<cwith|2|10|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|iden><rsub|A>|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>*<around*|(|r|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|B|)>+max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><around*|(|r|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|bitSize<around*|(|B|)>|)>-r|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|unit><rsub|A>|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|injl><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO<rsub|>><rsub|dyn><around*|(|<math-ss|injr><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><around*|(|r|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|r|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><rsup|><around*|(|0|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|r|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|take><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|drop><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>>>
  </eqnarray*>

  <\lemma>
    For any core Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>><rsup|>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>=cellCount<around*|(|r<rsub|on,0>|)>+cellCount<around*|(|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>|)>>
      and<next-line><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|cellCount<around*|(|r<rsub|on,0>|)>|)>>
      and<next-line><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)><text|.>>
  </lemma>

  The problem with <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>
  is that it is effectively a dynamic analysis because its result is a
  function. We cannot direclty use this definition to perform a static
  analysis because we cannot cache and reuse results on shared
  sub-expressions. Fortuantely we can charaterize the set of possible
  functions returned by <math|extraCellsBound<rsup|TCO><rsub|dyn>> by a pair
  of parameters.

  <\equation*>
    interp<rsup|TCO><around*|\<langle\>|n,m|\<rangle\>><around*|(|r|)>\<assign\>max<around*|(|n-r,m|)>
  </equation*>

  We can write a static analysis to compute the pair of parameters that
  characterize the results of <math|extraCellsBound<rsup|TCO><rsub|dyn>>.

  <\eqnarray*>
    <tformat|<cwith|2|17|2|2|cell-halign|r>|<cwith|2|17|2|2|cell-halign|r>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|10|10|2|2|cell-halign|r>|<cwith|11|11|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|c>|<cwith|13|13|2|2|cell-halign|r>|<cwith|14|14|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|3|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|iden><rsub|A>|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|0,0|\<rangle\>>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>*>|<cell|\<assign\>>|<cell|<around*|\<langle\>|max<around*|(|r<rsub|b>+n<rsub|s>,n<rsub|t>,r<rsub|b>+m<rsub|t>|)>,r<rsub|b>+m<rsub|s>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|>|<cell|and>|<cell|r<rsub|b>\<assign\>bitSize<around*|(|B|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|unit><rsub|A>|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|0,0|\<rangle\>>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|injl><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO<rsub|>><rsub|static><around*|(|<math-ss|injr><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|max<around*|(|n<rsub|s>,n<rsub|t>|)>,max<around*|(|m<rsub|s>,m<rsub|t>|)>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|n<rsub|t>,max<around*|(|n<rsub|s>,m<rsub|s>,m<rsub|t>|)>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|take><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|drop><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>>>
  </eqnarray*>

  When computing <math|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>
  resulting values for shared sub-expressions can be shared, making
  <math|extraCellsBound<rsup|TCO><rsub|static>> a static analysis. We can use
  <math|interp<rsup|TCO>> and <math|extraCellsBound<rsup|TCO><rsub|static>>
  to compute <math|extraCellsBound<rsup|TCO><rsub|dyn>> for our bound on cell
  count.

  <\lemma>
    <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>=interp<rsup|TCO><around*|(|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>|)>>.
  </lemma>

  <\corollary>
    For any core Simplicity expression <math|t:A\<vdash\>B> and <math|a:A>
    such that

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+max<around*|(|n,m|)><text|>>

    <no-indent>where <math|<around*|\<langle\>|n,m|\<rangle\>>\<assign\>><math|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>.
  </corollary>

  <subsubsection|Maximum Frame Count Bound>

  <subsection|Time Resources>

  <section|Commitment Merkle Root>

  In modern Bitcoin, users who use P2SH (pay to script hash) do not commit
  funds directly to Script, rather they commit to a hash of their Script.
  Only when they wish to redeem their funds do they reveal their Script for
  executation. Bitcoin's concensus protocol enforces that the Script
  presented during redemption has a hash that matches the commited hash.

  <assign|cmr|<macro|x|<math|#<rsup|c><around*|(|<arg|x>|)>>>>Simplicity is
  designed to work in the same way. However, instead of a linear hash of a
  serialized Simplicity program (Section<nbsp><reference|Serialization>) we
  follow the tree structure of a Simplicity expression and compute a
  commitment Merkle root of the syntax tree. Below we define the commitment
  merkle root of a Simplicity expression <math|t\<of\>A\<vdash\>B> as a
  256-bit value <cmr|t>.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|iden>>>>|<row|<cell|<cmr|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|comp>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|unit>>>>|<row|<cell|<cmr|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|injl>>\<comma\>
    <around*|\<langle\>|\<b-0\>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|injr>>\<comma\>
    <around*|\<langle\>|\<b-0\>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|pair>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|take>>\<comma\>
    <around*|\<langle\>|\<b-0\>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|drop>>\<comma\>
    <around*|\<langle\>|\<b-0\>,<cmr|t>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  Here we are directly using SHA-256's compression function,
  <math|SHA256Block<around*|\<langle\>|i,b|\<rangle\>>>, which takes two
  arguments. The first argument, <math|i>, is a 256-bit initial value. The
  second value, <math|b>, is a 512-bit block of data. Above we divide a block
  into two 256-bit values, <math|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>>,
  and recursively pass Merkle roots into the compression function. We write
  <math|\<b-0\>> for a suitably long sequence of 0 bits.

  Like static analysis, the time needed to computing the commitment Merkle
  root is linear in the size of the DAG representing the term because the
  intermediate results on sub-expressions can be shared.

  We define unique inital values <math|tag<rsup|c><rsub|x>> for every
  combinator by taking the SHA-256 hash of unique byte strings:

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|iden>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f6964656e]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|comp>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f636f6d70]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|unit>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f756e6974]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injl>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f696e6a6c]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injr>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f696e6a72]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|case>>>|<cell|\<assign\>>|<math|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f63617365]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|pair>>>|<cell|\<assign\>>|<math|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f70616972]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|take>>>|<cell|\<assign\>>|<math|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f74616b65]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|drop>>>|<cell|\<assign\>>|<math|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f64726f70]>>>>>
  </eqnarray*>

  Notice that the type annotations for expressions are not included in the
  commitment Merkle root. We will rely on type inference to derive principle
  type annotations. Later, we will make use of this flexibilty when pruning
  unused branches from <samp|case> expressions.

  <section|Serialization><label|ss:Serialization>

  <subsection|Type Inference>

  <chapter|Simplicity Extensions>

  Theorem<nbsp><reference|thm:CSCT> proves that the core Simplicity language
  is already computationally complete. Our primary method of extending
  Simplicity is by adding expressions with side-effects. We will use monads
  to formally specify these new effects.

  <section|Monadic Effects>

  A functor <math|\<cal-F\>> maps types, <math|A>, to types
  <math|\<cal-F\>A>, and maps function <math|f : A\<rightarrow\>B> to
  functions <math|\<cal-F\>f : \<cal-F\>A \<rightarrow\>\<cal-F\>B>. This
  mapping is required to satify natural laws.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-F\>id>|<cell|=>|<cell|id>>|<row|<cell|\<cal-F\><around*|(|f\<circ\>g|)>>|<cell|=>|<cell|\<cal-F\>f\<circ\>\<cal-F\>g>>>>
  </eqnarray*>

  A moand, <math|\<cal-M\>>, is a functor that comes with two natural
  transformations.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|:>|<cell|A
    \<rightarrow\> \<cal-M\>A>>|<row|<cell|\<mu\><rsup|\<cal-M\>><rsub|A>>|<cell|:>|<cell|\<cal-M\>\<cal-M\>A\<rightarrow\>\<cal-M\>A>>>>
  </eqnarray*>

  where forall <math|f\<of\>A\<rightarrow\>B>,

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-M\>f\<circ\>\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|\<eta\><rsup|\<cal-M\>><rsub|B>\<circ\>f>>|<row|<cell|\<cal-M\>f\<circ\>\<mu\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|\<mu\><rsup|\<cal-M\>><rsub|B>\<circ\>\<cal-M\>\<cal-M\>f>>>>
  </eqnarray*>

  The <math|\<eta\><rsup|\<cal-M\>><rsub|A>> and
  <math|\<mu\><rsup|\<cal-M\>><rsub|A>> functions required to satisfy certain
  coherence laws. The monad laws are best presented using Kleisli morphisms.

  <subsection|Kleisli Morphisms>

  Functions from <math|A> to <math|B> that produce side-effects are
  represented by Kleisli morphisms, which are (pure) functions <math|A
  \<rightarrow\>\<cal-M\>B>, where <math|\<cal-M\>> is a monad that captures
  the particular side-effects of the function in the result type. For Kleisli
  morphisms <math|f\<of\>A\<rightarrow\>\<cal-M\>B> and
  <math|g\<of\>B\<rightarrow\>\<cal-M\>C> we define the Kleisli composition
  of them as <math|g<op|\<leftarrowtail\><rsup|\<cal-M\>>>f\<of\>A\<rightarrow\>\<cal-M\>C>
  where

  <\equation*>
    g<op|\<leftarrowtail\>><rsup|\<cal-M\>>f\<assign\>\<mu\><rsup|\<cal-M\>>\<circ\>\<cal-M\>g\<circ\>f
  </equation*>

  We will usually omit the annotation.

  The monad laws can be presented in terms of Kleisli composition. For all
  <math|f\<of\>A\<rightarrow\>\<cal-M\>B>, <math|g\<of\>B
  \<rightarrow\>\<cal-M\>C>, and <math|h:C\<rightarrow\>\<cal-M\>D>, we
  require that Kleisli composition satify the laws of composition with
  <math|\<eta\><rsup|\<cal-M\>>> as its identity:

  <\eqnarray*>
    <tformat|<table|<row|<cell|f\<leftarrowtail\>\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|f>>|<row|<cell|\<eta\><rsup|\<cal-M\>><rsub|B>\<leftarrowtail\>f>|<cell|=>|<cell|f>>|<row|<cell|<around*|(|h\<leftarrowtail\>g|)>\<leftarrowtail\>f>|<cell|=>|<cell|h\<leftarrowtail\><around*|(|g\<leftarrowtail\>f|)>>>>>
  </eqnarray*>

  <subsection|Cartesian Strength>

  In addition to Kleisli composition, we define a series of helper functions
  for manupulating products.\ 

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|\<beta\><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:A\<times\>\<cal-M\>B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|\<beta\><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>>|<cell|<math|\<assign\>
  \<cal-M\><around*|(|\<lambda\>x\<point\><around*|\<langle\>|a,x|\<rangle\>>|)><around*|(|b|)>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|<wide|\<beta\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>A\<times\>B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|<wide|\<beta\>|\<bar\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>>|<cell|<math|\<assign\>
  \<cal-M\><around*|(|\<lambda\>x\<point\><around*|\<langle\>|x,b|\<rangle\>>|)><around*|(|a|)>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|\<phi\><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>A\<times\>\<cal-M\>B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|\<phi\><rsup|\<cal-M\>>>>|<cell|<math|\<assign\>\<beta\><rsup|\<cal-M\>>\<leftarrowtail\><wide|\<beta\>|\<bar\>><rsup|\<cal-M\>>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>A\<times\>\<cal-M\>B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>>>>|<cell|<math|\<assign\><wide|\<beta\>|\<bar\>><rsup|\<cal-M\>>\<leftarrowtail\>\<beta\><rsup|\<cal-M\>>>>>>>>>

  \;

  The operations <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>> and
  <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>> are similar, but
  differ in the order that effects are applied in. Roughly speaking,
  <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>> applies the effects of the first
  component first, while <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>
  applies the effects of the second component first. For some monads, the
  order of the effects is immaterial and <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>.
  We call such monads, <dfn|commutative monads>.

  It is always the case that

  <\equation*>
    \<phi\><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>A>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>A>\<of\>\<cal-M\>A\<rightarrow\>\<cal-M\><around*|(|A<rsup|2>|)>
  </equation*>

  holds, even for non-commutative monads. In this case, the effect specified
  by the input is duplicated. Compare this with
  <math|<math|\<cal-M\>\<Delta\><rsub|A>\<of\>\<cal-M\>A\<rightarrow\>\<cal-M\><around*|(|A<rsup|2>|)>>>
  where the contents of type <math|A> are duplicated, but not the effect
  itself. When we have <math|\<cal-M\>\<Delta\><rsub|A>=\<phi\><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>A>>
  <around*|(|<text|equiv.> <math|\<cal-M\>\<Delta\><rsub|A>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>A>>|)>,
  we say that <math|\<cal-M\>> is an <dfn|idempotent monad>.
  <with|color|red|TODO: note about King and Wadler.> For idempotent monads,
  the same effect is occuring two or more times in a row is equivalent to it
  occuring once.

  <subsection|Monadic Semantics>

  \;

  We define a new intepretation of Simplicity expressions,
  <math|t\<of\>A\<vdash\>B>, whose denotations are these Kleisli morphisms,
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<of\>A\<rightarrow\>\<cal-M\>B>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|iden><rsub|A>|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|comp><rsub|A,B,C>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><op|\<leftarrowtail\>><around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|unit><rsub|A>|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><around*|\<langle\>||\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|injl><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<cal-M\><injl|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|)>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|injr><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<cal-M\><injr|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|)>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|b,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|pair><rsub|A,B,C>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<phi\><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>,
    <around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|take><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|drop><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|b|)>>>>>
  </eqnarray*>

  The above interpretation for Kleisli morphisms is nearly uniquely defined
  if we require parametericity. Many well-typed variations of the definition
  above end up being equivalent due to the monad laws. The main choice we
  have is between using <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>> or
  <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>> in the definition
  of <math|<around*|\<llbracket\>|<math-ss|pair> s
  t|\<rrbracket\>><rsup|\<cal-M\>>>. The only other definitions amount to
  duplicating the effects of sub-expressions.

  To ensure that all these possible choices are immaterial, we demand that
  <math|\<cal-M\>> be a commutative, idempotent monad when interpreting
  Simplicity expressions. This lets us ignore the order of effects, and
  duplication of effects, which simplifies reasoning about Simplicity
  programs. It also provides an opportunity for a Simplicity optimizer to,
  for example, reorder pairs without worrying about changing the denotational
  semantics.

  <\theorem>
    For any core Simplicity expression, <math|t\<of\>A\<vdash\>B>, we have
    <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<assign\>\<eta\><rsup|\<cal-M\>><rsub|B>\<circ\><around*|\<llbracket\>|t|\<rrbracket\>>>.
  </theorem>

  <subsubsection|Identity Monad>

  The most trivial monad is the identity monad, <math|Id>, where
  <math|Id\<space\>A\<assign\>A> and <math|Id\<space\>f\<assign\> f>. The
  natural transformations <math|\<eta\><rsup|Id><rsub|A>> and
  <math|\<mu\><rsup|Id><rsub|A>> are both the idenity function. The identity
  monad captures no side-effects. It is commutative and idempotent.

  <\corollary>
    For any core Simplicity expression, <math|t\<of\>A\<vdash\>B>, we have
    <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|Id>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>>>.
  </corollary>

  <section|Witness>

  Our first extension to core Simplicity is the witness expression. The
  langauge that uses this extension is called <dfn|Simplicity with
  witnesses>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|b\<of\>B>>>|<row|<cell|<math|<math-ss|witness><rsub|A,B>
    b \<of\>A\<vdash\>B>>>>>>
  </with>

  \;

  The denotational semantics of the witness expression is simply a constant
  function that returns its parameter.

  \;

  <\equation*>
    <around*|\<llbracket\>|<math-ss|witness><rsub|A,B>
    b|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>\<assign\>\<eta\><rsup|\<cal-M\>><rsub|B><around*|(|b|)>
  </equation*>

  As far as semantics goes, this extension doesn't provide any new
  expressivity. A constant function for any value <math|b> can already be
  expressed in core Simplicity using combinations of <samp|unit>,
  <samp|injl>, <samp|injr>, and <samp|pair>. The difference between this and
  the <samp|witness> expressions lies in its commitment Merkle root.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|witness><rsub|A,B>
    b>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|witness>>>>>>
  </eqnarray*>

  The <math|tag<rsup|c><rsub|<math-ss|witness>>> value is derived as the
  SHA-256 hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|witness>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f7769746e657373]>>>>>
  </eqnarray*>

  Notice that a <math|<samp|witness> b> expression does commit to its
  parameter in the commitment root. This means that at redemption time a
  <samp|witness> expression's parameter, called a <dfn|witness value>, can be
  set to any value.

  Witness values play the same role as Bitcoin Script's input stack in its
  <verbatim|sigScript> or Segwit's <verbatim|witness>. They act as inputs to
  Simplicity programs. Rather than accepting arguments as inputs and passing
  them down to where they are needed, <samp|witness> expressions lets input
  data appear right where it is needed.

  <subsection|Elided Computation>

  <subsection|Witness Merkle Root>

  <subsection|Serialization with Witnesses>

  <subsection|Type Inference with Witness>

  Like other expressions, a <samp|witness> expression doesn't commit to its
  type in its commitment Merkle root. Type inference is used to compute the
  minimal type needed for each witness expression. This ensures that third
  parties cannot perform witness malleation to it with unused data on
  transactions during transit.

  <section|Assertions and Failure>

  Our first side-effect will be aborting a computation. New assertion and
  <samp|fail> expressions make use of this effect. The langauge that uses
  this extension is called <dfn|Simplicity with assertions>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<times\>C\<vdash\>D>>|<cell|<math|h
    \<of\><2><rsup|256>>>>>>>>>|<row|<cell|<math|<math-ss|assertl><rsub|A,B,C,D>
    s h: <around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|h\<of\><2><rsup|256>>>|<cell|<math|t
    : B\<times\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|assertr><rsub|A,B,C,D>
    h t: <around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|h\<of\><2><rsup|512>>>>|<row|<cell|<math|<math-ss|fail><rsub|A,B>
    h \<of\>A\<vdash\>B>>>>>>
  </with>

  \;

  Assertions serve a dual purpose. One purpose is to replicate the behaviour
  of Bitcoin Script's <verbatim|OP_VERIFY> and similar operations that are
  used to validate checks on programable conditions, such as verifying that a
  digital signature verificaiton passes and causing the program to abort
  otherwise.

  The second purpose is to support pruning of unsued <samp|case> branches
  during redemption. The 256-bit value is used in the commitment Merkle root
  computation to hold Merkle root of the pruned braches. This will be covered
  in Section<nbsp><reference|ss:pruning>.

  Because we are extending Simplicty's semantics to support an abort effect,
  there is no harm in adding a generic <samp|fail> expression. The parameter
  to the <samp|fail> expression is used to support salted expressions (see
  Section<nbsp><reference|ss:salted>). We will see that <samp|fail>
  expressions never manifest themselves within a blockchain's concensus
  protocol.

  <subsection|Monad Zero><label|ss:MonadZero>

  To give monadic semantics to the assertion and <samp|fail> expressions, we
  will require that the monad capturing the our effects have a <dfn|zero>

  <\equation*>
    \<emptyset\><rsup|\<cal-M\>><rsub|A>\<of\>\<cal-M\>A
  </equation*>

  where forall <math|f\<of\>A\<rightarrow\>B>,

  <\equation*>
    \<cal-M\>f<around*|(|\<emptyset\><rsup|\<cal-M\>><rsub|A>|)>=\<emptyset\><rsup|\<cal-M\>><rsub|B>
  </equation*>

  This zero effect captures the notion of a failed, or aborted computation.

  The laws for these monads with zero are, again, best expressed using
  Kleisli morphsisms. At the risk of some notational confusion, we define
  <math|\<varnothing\><rsup|\<cal-M\>><rsub|A,B>\<of\>A\<rightarrow\>\<cal-M\>B>
  as a <dfn|zero morphism>.

  <\equation*>
    \<varnothing\><rsup|\<cal-M\>><rsub|A,B><around*|(|a|)>\<assign\>
    \<emptyset\><rsup|\<cal-M\>><rsub|B>
  </equation*>

  Zero morphisms are required to be an absorbing element for Kleisli
  compostion. For all <math|f\<of\>A\<rightarrow\>\<cal-M\>B> and
  <math|g\<of\>B \<rightarrow\>\<cal-M\>C> we require that

  <\eqnarray*>
    <tformat|<table|<row|<cell|g<op|\<leftarrowtail\>>\<varnothing\><rsup|\<cal-M\>><rsub|A,B>>|<cell|=>|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|A,C>>>|<row|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|B,C><op|\<leftarrowtail\>>f>|<cell|=>|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|A,C>>>>>
  </eqnarray*>

  (Note: In Haskell, the <verbatim|mzero> value typically is only required to
  satify the first law; however, we require monads with zero to satify both
  laws.)

  <subsection|Denotational Semantics>

  Given an commutative, idempotent monad with zero, <math|\<cal-M\>>, we
  extend the monadic semantics for Simplicity expressions,
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>>, to include
  assertion expressions:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|assertl><rsub|A,B,C,D>
    s h|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertl><rsub|A,B,C,D>
    s h|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|D>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertr><rsub|A,B,C,D>
    h t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|D>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertr><rsub|A,B,C,D>
    h t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|b,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|fail><rsub|A,B>
    h|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|B>>>>>
  </eqnarray*>

  Notice that the <math|h> parameters are ignored in the semantics. They will
  be used instead in for the Merkle root definitions in
  Section<nbsp><reference|ss:AssertMerkleRoot>.

  <subsubsection|Option Monad>

  <assign|maybe|<math|<math-up|S>>>We define the functor <math|<value|maybe>>
  as the option monad, also known as the maybe monad:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<maybe>A>|<cell|\<assign\>>|<cell|<value|1>+A>>|<row|<cell|<maybe>f<around*|(|<injl|<around*|\<langle\>||\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|<injl|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|<maybe>f<around*|(|<injr|<around*|(|a|)>>|)>>|<cell|\<assign\>>|<cell|<injr|<around*|(|f<around*|(|a|)>|)>>>>>>
  </eqnarray*>

  The monad operations are defined as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|<injr|<around*|(|a|)>>>>|<row|<cell|\<mu\><rsup|S><rsub|A><around*|(|<injl|<around*|\<langle\>||\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|<injl|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|\<mu\><rsup|S><rsub|A><around*|(|<injr|<around*|(|x|)>>|)>>|<cell|\<assign\>>|<cell|x>>>>
  </eqnarray*>

  The option monad is commutative and idempotent. The option monad has a
  zero:

  <\equation*>
    \<emptyset\><rsup|<maybe>><rsub|A>\<assign\><injl|<around*|\<langle\>||\<rangle\>>>
  </equation*>

  Therefore, a term in the language of core Simplicity extended with
  witnesses and failure, <math|t\<of\>A\<vdash\>B>, can be intepreted as a
  function returning an optional result: <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|<maybe>>:A\<rightarrow\><maybe>B>.

  There is a natural transformation from the option monad into any monad with
  zero, <math|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<of\><maybe>A\<rightarrow\>\<cal-M\>A>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A><around*|(|\<emptyset\><rsup|<maybe>><rsub|A>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|A>>>|<row|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A><around*|(|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><rsub|A><around*|(|a|)>>>>>
  </eqnarray*>

  <\lemma>
    For all <math|f :A\<rightarrow\>B>,

    \;

    <\equation*>
      \<iota\><rsup|\<cal-M\>><rsub|<maybe>,B>\<circ\><maybe>f=\<cal-M\>f\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>
    </equation*>

    Also

    <\equation*>
      \<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<circ\>\<mu\><rsup|<maybe>><rsub|A>=\<mu\><rsup|\<cal-M\>><rsub|A>\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,\<cal-M\>A>\<circ\><maybe>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>
      <around*|(|=\<mu\><rsup|\<cal-M\>><rsub|A>\<circ\>\<cal-M\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,<maybe>A>|)>
    </equation*>
  </lemma>

  <\theorem>
    For any core Simplicity expression with assertions,
    <math|t\<of\>A\<vdash\>B>, and any commutative idempotent monad with zero
    <math|\<cal-M\>>, we have <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<assign\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,B>\<circ\><around*|\<llbracket\>|t|\<rrbracket\>><rsup|<maybe>>>.
  </theorem>

  <subsection|Merkle Roots><label|ss:AssertMerkleRoot>

  We extend the definition of commitment Merkle root to support the new
  assertion and <samp|fail> expressions

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|assertl><rsub|A,B,C,D>
    s h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|<cmr|s>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|assertr><rsub|A,B,C,D>
    h t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|h,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|fail><rsub|A,B>
    h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|fail>>,h|\<rangle\>>>>>>
  </eqnarray*>

  The <math|tag<rsup|c><rsub|<math-ss|fail>>> value is derived as the SHA-256
  hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|fail>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f6661696c]>>>>>
  </eqnarray*>

  It is important to notice that we are reusing
  <math|tag<rsup|c><rsub|<math-ss|case>>> when tagging assertions in their
  commitment Merkle root. Also notice that the <math|h> value, which was
  ignored in the semantics, is used in the commitment Merkle root. Together
  this can allow an assertion expression to substitute for a case expression
  at redeption time while maintaining the same commitment Merkle root. This
  enables a feature of Simplicity called pruning, which is detailed in
  Section<nbsp><reference|ss:pruning>.

  \;

  <subsubsection|Pruning Unused <samp|case> Branches><label|ss:pruning>

  The commitment Merkle roots of the assertion expression reuses
  <math|tag<rsup|c><rsub|<math-ss|case>>> in the compression function. This
  means that the following identies hold.

  <\equation*>
    <cmr|<math-ss|assertl><rsub|A,B,C,D> s
    <cmr|t>>=<cmr|<math-ss|case><rsub|A,B,C,D> s
    t>=<cmr|<math-ss|assertr><rsub|A,B,C,D> <cmr|s> t>
  </equation*>

  In particular, it means that when a <math|<math-ss|case>> expression is
  used at commitment time, it can be replaced by an assertion expression. If
  we substitute a <samp|case> with an assertion expression and that assertion
  fails during evalutation, then the whole transaction will be deemed invalid
  and rejected. On the other hand if the assertion does not fail, then we are
  guarenteed to end up with the same result (which ultimately could still be
  failure due to a latter assertion failure). Therefore, assuming the
  transaction is valid, the subsitution of assertions will not change the
  semantics.

  We can take advantage of this by performing this substituion at redemption
  time. We can effiecively replace any unused branch in a case expression
  with its commitment Merkle root. In fact, we will require this replacement
  to occur during redemption.

  For those cases where we want to use an assertion at commitment time, for
  example when performing something similar to Bitcoin Script's
  <verbatim|OP_VERIFY>, we use <samp|case> with <samp|fail>, as in

  <\equation*>
    <math-ss|case> <around*|(|<math-ss|fail> \<b-0\>|)> t
  </equation*>

  where <math|\<b-0\>\<of\><2><rsup|512>> is a vector of zero bits, which is
  used as a canonical parameter for <samp|fail>. During redemption this
  <samp|case> experssion will be required to be pruned and replaced with an
  assertion expression:

  <\equation*>
    <math-ss|assertr> <cmr|<math-ss|fail> \<b-0\>> t
  </equation*>

  Naturally, the <math|\<b-0\>> paramter can be replaced with any value; this
  can be used as a method of salting expression, which is the subject of the
  next section.

  <subsubsection|Salted Expressions><label|ss:salted>

  During pruning, usused branches are replaced by its commitment Merkle root.
  Since hashes are one way functions, one might believe that third parties
  will be unable to recover the pruned branch from just its commitment Merkle
  root. However, this argument is not so straightforward. Whether or not the
  expression can be recovered from just its commitment Merkle root depends on
  how much entropy the pruned expression contains. Third parties can grind,
  testing many different expressions, until they find one whose commitment
  Merkle root matches the one occuring in the assertion. If the entropy of
  the pruned expression is low, then this grinding is feasible.

  Some expressions naturally have high entropy. For example, any branch that
  contains a commitment to a public key will have at least the entropy of the
  public key space. However, this only holds so long as that public key isn't
  reused nor will ever be resued elsewhere.

  For expressions that need to reuse public keys, or otherwise naturally
  having low entropy, one can add salt, which is random data, to increase its
  entropy. There are several possible ways to incorporate random data into a
  Simplicity expression without altering the program's semantics. The most
  direct way is to incorporate the <samp|fail> expression which lets us
  directly incorporate random into is commitment Merkle root.

  Given a block of random data, <math|h : <2><rsup|512>>, and a Simplicity
  expression <math|t\<of\>A\<vdash\>B>, we can define two salted variants of
  <math|t>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|salted><rsup|0> h
    t>|<cell|\<assign\>>|<cell|<math-ss|witness>
    <math-ss|false>\<times\><math-ss|iden> ;<math-ss|assertl>
    <around*|(|<math-ss|drop> t|)> <cmr|<math-ss|fail> h> : A
    \<vdash\>B>>|<row|<cell|<math-ss|salted><rsup|1> h
    t>|<cell|\<assign\>>|<cell|<math-ss|witness>
    <math-ss|true>\<times\><math-ss|iden> ;<math-ss|assertr>
    <cmr|<math-ss|fail> h> <around*|(|<math-ss|drop> t|)> : A \<vdash\>B>>>>
  </eqnarray*>

  The <math|<math-ss|salted><rsup|i> h t> experssion will have high entropy
  so long as the random data <math|h> has high entropy. By randomly chosing
  between these two variants, this method of salting obsurces the fact that
  the expression is salted at all, in cases where this expression ends up
  being revield during redemption. Without knowing <math|h>, it is
  impractical to determine if <math|#<rsup|c><around*|(|<math-ss|fail> h|)>>
  is the commitment Merkle root of a <samp|fail> expression, or if it is a
  some other, high-entropy, alternate expression that the redeemer has simply
  choosen not to execute.

  By explicitly using the <samp|fail> expression here, one has the option
  prove that these alternative branches are unexecutable by revealing the
  value <math|h>. If the Simplicity expression is part of a multi-party
  contract, it maybe required to reveal <math|h> (or prove in zero-knowledge
  that such an <math|h> exists) to all party members so everyone can vet the
  security properties of the overall smart contract.

  <section|Blockchain Primitives>

  We entend Simplicity with primitive expressions that provide blockchain
  specific features. Naturally the specifics of these primtive expressions
  depends on the specific blockchain application, but generally speaking the
  primitives allow reading data from the context that a Simplicity program is
  being evaluated within. This is usually the data of the encompasing
  transaction including details about the inputs and outputs of the
  transaction, and which specific input is being evaluated.

  A blockchain application needs to provide a set of typed primitive
  expressions and a monad to capture the side-effects for these primitives.
  This monad should be a commutative, idempotent monad with zero in order to
  interpret Simplicity and its extenstions. All primitive expressions must be
  monomorphic and have no parameters (i.e. they are not themselves
  combinators).

  In this document we will be detailing the primitives used for Bitcoin, or a
  Bitcoin-like application.

  <subsection|Bitcoin Transactions><label|ss:BitcoinTransactions>

  For the Bitcoin application, Simplicity's primitives will be primarily
  focuses on accessing the <dfn|signed transaction data>, which is the data
  that is hashed and signed in Bitcoin.

  We define a record type that captures this context, called <math|BCEnv>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|Lock>|<cell|\<assign\>>|<cell|<2><rsup|32>>>|<row|<cell|Value>|<cell|\<assign\>>|<cell|<2><rsup|64>>>|<row|<cell|Outpoint>|<cell|\<assign\>>|<cell|<2><rsup|256>\<times\><2><rsup|32>>>|<row|<cell|SigInput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|prevOutpoint\<of\>Outpoint>>|<row|<cell|value\<of\>Value>>|<row|<cell|sequence\<of\><2><rsup|32>>>>>>|}>>>|<row|<cell|SigOutput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|value\<of\>Value>>|<row|<cell|pubScript\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>>>>>|}>>>|<row|<cell|SigTx>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|version\<of\><2><rsup|32>>>|<row|<cell|inputs\<of\>SigInput<rsup|+>>>|<row|<cell|outputs\<of\>SigOutput<rsup|+>>>|<row|<cell|lockTime\<of\>Lock>>>>>|}>>>|<row|<cell|BCEnv>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|tx\<of\>SigTx>>|<row|<cell|ix\<of\><2><rsup|32>>>|<row|<cell|scriptCMR\<of\><2><rsup|256>>>>>>|}>>>>>
  </eqnarray*>

  The type <math|SigTx> contains the signed transaction data. Following a
  design similar to BIP 143, this signed transaction data excludes
  transaction inputs' sigScripts and includes inputs' Bitcoin values. The
  <math|ix> field is input index whose redemption is being processed by this
  Simplicity program. The <math|scriptCMR> field holds the commitment Merkle
  root of the Simplicity program being evaluated.

  The SigTx type given above allows for an unbounded number of inputs and
  ouputs. However, there are limits imposed by the Bitcoin protocol. The
  number of inputs and outputs are limited to at most <math|2<rsup|32>-1> by
  Bitcoin's deserialization implementation. Similarly, the length of
  SigOutput's pubScript is limited to at most <math|2<rsup|32>-1> bytes. We
  presume all transactions to adhere to these limits when reasoning about
  Bitcoin transactions.\ 

  Furthemore, we presume that for every <math|e\<of\>BCEnv> that
  <math|<around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>\<less\><around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>>
  so that ``current'' index being validated is, in fact, an input of the
  transaction. <with|color|red|TODO moneyRange>

  <assign|BC|<math|BC>>The monad we use for the Bitcoin application provides
  an environment effect (also known as a reader effect) that allows read
  access to the <math|BitcoinEnv> value defining the Simplicity program's
  evaluation context. We call this monad <math|BC>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<BC>A>|<cell|\<assign\>>|<cell|BCEnv\<rightarrow\><maybe>A>>|<row|<cell|<BC>f<around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>
    <maybe>f<around*|(|a<around*|(|e|)>|)>>>>>
  </eqnarray*>

  \;

  <BC> is a commutative, idempotent monad with zero:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|<BC>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>
    \<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>>|<row|<cell|\<mu\><rsup|<BC>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>
    \<mu\><rsup|<maybe>><rsub|A><around*|(|<maybe><around*|(|\<lambda\>f\<point\>f<around*|(|e|)>|)><around*|(|a<around*|(|e|)>|)>|)>>>|<row|<cell|\<emptyset\><rsup|<BC>><rsub|A>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>
    \<emptyset\><rsup|<maybe>><rsub|A>>>>>
  </eqnarray*>

  \;

  We define several new primitive expressions for reading data from a
  <math|BCEnv> value. The langauge that uses this extension is called
  <dfn|Simplicity with Bitcoin>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|version>
    : <value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|lockTime>
    : <value|1>\<vdash\>Lock>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputsHash>
    : <value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputsHash>
    : <value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numInputs>
    : <value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|totalInputValue>
    : <value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentPrevOutpoint>
    : <value|1>\<vdash\>OutPoint>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentValue>
    : <value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentSequence>
    : <value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIndex>
    : <value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputPrevOutpoint>
    : <2><rsup|32>\<vdash\><maybe><around*|(|Outpoint|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputValue>
    : <2><rsup|32>\<vdash\><maybe><around*|(|Value|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputSequence>
    : <2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|32>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numOutputs>
    : <value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|totalOutputValue>
    : <value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputValue>
    : <2><rsup|32>\<vdash\><maybe><around*|(|Value|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputScriptHash>
    : <2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|scriptCMR>
    : <value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  <subsubsection|Denotational Semantics><label|ss:BTDenotationalSemantics>

  We extend the formal semantics of these new expressions as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|version>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|version|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|lockTime>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|lockTime|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputsHash>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>inputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputsHash>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>outputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numInputs>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|totalInputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|fold<rsup|<around*|\<lfloor\>|+|\<rfloor\>><rsub|64>><around*|(|<around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentPrevOutpoint>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentSequence>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIndex>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|ix|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputPrevOutpoint>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputValue>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputSequence>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numOutputs>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|outputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|totalOutputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|fold<rsup|<around*|\<lfloor\>|+|\<rfloor\>><rsub|64>><around*|(|<around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputValue>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputScriptHash>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>SHA256<around*|(|l<around*|[|pubScript|]>|)>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|scriptCMR>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|:=>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|scriptCMR|]>|)>>>>>
  </eqnarray*>

  where

  <\eqnarray*>
    <tformat|<table|<row|<cell|inputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|BE<rsub|<2><rsup|256>><around*|(|\<pi\><rsub|1><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|<2><rsup|32>><around*|(|\<pi\><rsub|2><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|<2><rsup|32>><around*|(|l<around*|[|sequence|]>|)>>>|<row|<cell|ouputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|LE<rsub|<2><rsup|64>><around*|(|l<around*|[|value|]>|)>\<cdummy\>BE<rsub|<2><rsup|256>><around*|(|SHA256<around*|(|l<around*|[|pubScript|]>|)>|)>>>>>
  </eqnarray*>

  and where <math|LE<rsub|<2><rsup|n>>\<of\><2><rsup|n>\<rightarrow\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>
  and <math|BE<rsub|<2><rsup|n>>\<of\><2><rsup|n>\<rightarrow\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>
  are little endian and big endian encodings of words of sutiably large size
  as byte strings.

  <\eqnarray*>
    <tformat|<table|<row|<cell|LE<rsub|<2><rsup|8>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<ast\>><around*|(|a|)>>>|<row|<cell|LE<rsub|<2><rsup|2*n>><around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>>|<cell|\<assign\>>|<cell|LE<rsub|<2><rsup|n>><around*|(|a<rsub|2>|)>\<cdummy\>LE<rsub|<2><rsup|n>><around*|(|a<rsub|1>|)><text|<htab|5mm>(when
    <math|8\<leq\>n>)>>>|<row|<cell|BE<rsub|<2><rsup|8>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<ast\>><around*|(|a|)>>>|<row|<cell|BE<rsub|<2><rsup|2*n>><around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>>|<cell|\<assign\>>|<cell|BE<rsub|<2><rsup|n>><around*|(|a<rsub|1>|)>\<cdummy\>BE<rsub|<2><rsup|n>><around*|(|a<rsub|2>|)><text|<htab|5mm>(when
    <math|8\<leq\>n>)>>>>>
  </eqnarray*>

  <with|color|red|Consider making everything big endian?>

  For most of these primitive expressions, it is clear that they can never
  fail, in the sense of never returning <math|\<emptyset\><rsup|<maybe>>>.
  The expressions <math|<around*|\<llbracket\>|<samp|currentPrevOutpoint>|\<rrbracket\>><rsup|BC>>,
  <math|<around*|\<llbracket\>|<samp|currentValue>|\<rrbracket\>><rsup|BC>>
  and <math|<around*|\<llbracket\>|<samp|currentSequence>|\<rrbracket\>><rsup|BC>>
  look like they could fail under some circumstances; however the assumption
  that for every <math|e\<of\>BCEnv> that
  <math|<around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>\<less\><around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>>
  implies that those expressions cannot fail either.

  <subsubsection|Merkle Roots><label|ss:BTMerkleRoots>

  We extend the definition of commitment Merkle root to support the new
  expressions by hashing new unique byte strings.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<cmr|<math-ss|version><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[76657273696f6e]>|)>>>|<row|<cell|<cmr|<math-ss|lockTime><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6c6f636b54696d65]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputsHash>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e7075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputsHash>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f75747075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numInputs>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6e756d496e70757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|totalInputValue>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[746f74616c496e70757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentPrevOutpoint>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e74507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentValue>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e7456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentSequence>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e7453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIndex>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e74496e646578]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputPrevOutpoint>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e707574507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputValue>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e70757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputSequence>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e70757453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numOutput>s><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6e756d784f757470757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|totalOutputValue>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[746f74616c4f757470757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputValue>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f757470757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|outputScriptHash><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f757470757453637269707448617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|scriptCMR>><rsub|>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[736372697074434d52]>|)>>>>>
  </eqnarray*>

  where

  <\equation*>
    BCprefix\<assign\><math-tt|[53696d706c69636974791f5072696d69746976651f426974636f696e1f]>
  </equation*>

  <subsubsection|Schnorr Signature Aggregation>

  <section|Malleability>

  <subsection|Transaction Weight>

  <chapter|Jets>

  <section|Example: The Standard Single Signature>

  <with|color|red|TODO: don't forget about lock parsing
  jets.><chapter|Delegation>

  Our last Simplicity extension is the <samp|disconnect> expression. This
  extention allows for delegation but using it loses some nice properties of
  Simplicity. The langauge that uses this extension is called <dfn|Simplicity
  with delegation>. The language that uses this and all other extensions is
  called <dfn|full Simplicity with delegation>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<times\><2><rsup|256>\<vdash\>B\<times\>C>>|<cell|<math|t
    : C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t: A\<vdash\>B\<times\>D>>>>>>
  </with>

  \;

  Semantically, the <samp|disconnect> expression behaves similar to the
  composition expression, but where the commitment Merkle root of the
  expression <math|t> is passed as an argument to the expression <math|s>. We
  extend the formal semantics to the <samp|disconnect> expression as follows.

  <\equation*>
    <around*|\<llbracket\>|<math|<math-ss|disconnect><rsub|A,B,C,D>> s
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>\<assign\>
    <around*|\<llbracket\>|s;<math-ss|take>
    <math-ss|iden>\<times\><math-ss|drop>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,<cmr|t>|\<rangle\>>
  </equation*>

  Like a <samp|witness> expression, the real signifigance comes from the form
  of its commitment Merkle root. We extend the definition of the commitment
  Merkle root as follows.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|disconnect>>\<comma\>
    <around*|\<langle\>|\<b-0\>,<cmr|s>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  where the <math|tag<rsup|c><rsub|<math-ss|disconnect>>> value is derived as
  the SHA-256 hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|disconnect>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f646973636f6e6e656374]>>>>>
  </eqnarray*>

  The commitment Merkle root only commits to the first argument, <math|s>, of
  a <samp|disconnect> expression. During redemption the second argument,
  <math|t>, can be freely set to any Simplicity expression. In order to place
  restrictions on what <math|t> is allowed to be, the commitment Merkle root
  of <math|t> is passed to <math|s> as an input. This way <math|s> is allowed
  to dynamically decide if <math|t> is an acceptable expression to be used
  here.

  The primary purpose of <samp|disconnect> is for delegation. In this
  scenario, <math|s>, validates that the commitment merkle root
  <math|<cmr|t>> is signed by a fixed public key. This lets a user postpone
  defining <math|t> until redemption time, but still maintaining full
  control, because any redeption requires their signature on <math|t>. For
  example, a user can have <math|t> return a public key. After commitment,
  but before redemption, the user can delegate authorisation to redeem these
  funds to a third party by signing the that party's key in this fashion.

  The <samp|disconnect> expression comes with some significant caveats.
  Because the whole program isn't commited to at commitment time, it is no
  longer possible to statically analyse the maximum resource costs for
  redemption before commitment. During redemption <math|t> could, a priori,
  perfrom arbitrarly much computation. Contrast this with the <samp|witness>
  expression, where type inference limits the size of the witness data, so
  such bounds are still possible to compute.

  Of course, depending on the specifics of the policy enforced by <math|s>,
  it may be possible to bound the maximum resource costs for redemption in
  specific cases. However, that depends on the details of <math|s> and there
  is no practical, universal algorithm that will work for any Simpliciy
  expression. Using <samp|disconnect> risks creating program that ends up
  impractical to redeem due to costs. This danger is why <samp|disconnect>
  isn't part of full Simplicity and it is instead considered an extension to
  be used with extreme caution.

  However, it is also important to notice that static analysis can be
  performed at redemption time. At that point time the <math|t> expression
  has been proviced and usual static analysis can proceed. Static analysis
  can be part of the consensus protocol, even when the <samp|disconnect>
  expression is used.

  <section|Unbounded Loops>

  <with|color|red|TODO: Type inference around disconnect may be tricky. Do we
  require solving for C and D first before running type inference on t? Do we
  infer types on the whole thing at once? We probably want to infer
  everything at once. There could be multiple parallel uses of delegation and
  the type variables may end up linking one output to the other's input
  and/or vice versa. This is something that cannot happen with <samp|witness>
  expressions because <samp|witness> expressions take no input.>

  <chapter|Coq Library Guide>

  The Coq development for Simplicity is found in the <verbatim|Coq/>
  directory. There are two subdirectories, <verbatim|Simplicity/> contains
  modules releated to Simplicity, and the <verbatim|Util/> directory has a
  few modules dedicated to other structures that are not by themselves
  specific to Simplicity, including a short hierarchy for commutitive and
  idempotent monad. \ We will focus on the contents of the
  <verbatim|Simplicity/> directory.

  <section|Simplicity Types>

  The Coq development for Simplicity begins with the
  <verbatim|Simplicity/Ty.v> file. This contain the inductive definition of
  <verbatim|Ty> which defines Simplicity's type expressions. The
  <verbatim|tySem> function interprets Simplicity types as Coq types, and it
  is declared as coercion. The module also provides standard arithmetic
  notation for Simplicity's sum and product types.

  The <verbatim|tyAlg> is a record collecting the operations needed to define
  structurally recursive functions for <verbatim|Ty>. \ These are known as
  <hlink|F-algebras|https://en.wikipedia.org/wiki/F-algebra>, and it is one
  of the inputs to <verbatim|tyCata> that defines catamorphisms from
  <verbatim|Ty> to another type.

  <section|Simplicity Terms>

  There are two different ways of representing of Simplicity terms defined in
  Coq. One representation is an ``inital'' representation, as an inductive
  types. The other representation is a ``final'' representation, as based on
  algebras for Simplicity.

  Generally speaking the ``initial'' representation works well when reasoning
  about Simplicity term using induction to prove properties about them, while
  the ``final'' representation is useful for implicitly capturing shared
  sub-expressions when defining Simplicity programs.

  We begin with the ``initial'' represetation, which will most readers will
  find more familiar.

  <subsection|The ``Initial'' Representation of Terms>

  The <verbatim|Simplicity/Core.v> module defines an inductive family,
  <verbatim|Term A B>, for the well-typed core Simplicity language. The core
  language is the pure fragment of Simplicity that has no effects such as
  failure or read access to the transaction environment. The <verbatim|eval>
  function provides denotational semantics and interprets terms as Coq
  functions over the corresponding Coq types.

  This module also establishes the Core Simplicity completeness theorem
  (Theorem <reference|thm:CSCT>) as the <verbatim|Simplicity_Completeness>
  theorem. The proof is built from <verbatim|scribe>, a function to produce
  Simplicity terms representing constant functions, and <verbatim|reify>
  which transforms Coq functions over Simplicity types into Simplicity terms
  representing those functions.

  <subsection|The ``Final'' Representation of Terms>

  To explain the ``final'' representation of terms it is first neccessary to
  understand what an algebra for Simplicity is. We can understand this by way
  of a mathematical analogy with ring theory. A ring is a mathematical
  structure consiting of a domain along with constants from that domain that
  correspond to 0 and 1, and binary functions over that domain that
  correspond to <math|\<noplus\>+> and <math|\<times\>> operations that
  satify certain ring laws. A term from the language of rings is an
  expression made out of <math|0>, <math|1>, <math|+>, and <math|\<times\>>.
  Given a ring and a term from the langauge of rings, we can intepret that
  term in the given ring and compute an element of the domain that the term
  represents. There are many different rings structures, such as the ring of
  integers, and the ring of integers modulo <math|n> for any positive number
  <math|n>. A given term can be interpreted as some value for any ring. It
  turns out that an alternative way to represent terms is as a function that
  given any ring returns a value from its domain and does so in a ``uniform''
  way. This would be the ``final'' representation for terms in the langauge
  of rings.

  <subsubsection|Simplicity Algebras>

  An algebra for Simplicity is an analgous structure to a ring. An algebra
  for Simplicity consists of a domain, along with constants from that domain
  that correspond to <math|<math-ss|iden>> and <math|<math-ss|unit>> and
  functions over that domain that correspond the other combinators from
  Simplicity. Unlike the case for rings, the domain of a Simplicity algebra
  is indexed by a pair of Simplicity types, and naturally the constants and
  functions that interpret Simplicity combinators must respect these types
  (and unlike rings, we are not going to impose any extra laws, making it a
  free-algebra).

  Core Simplicity algebras are formalized in the <verbatim|Simplicity/Alg.v>
  file. The <verbatim|Core.Class.class> record captures the interpretation of
  constants and combinators for core Simplicity over a given domain. The
  <verbatim|Core.Algebra> structure is the type of Simplicity algebras,
  containing a type family for the domain, and an instance of the
  <verbatim|Core.Class.class> record for interpretations.

  Given any Simplicity algebra and a well-typed term (from the ``initial''
  representation) we can interpret that term in the algebra to get out a
  value from the domain (that has a type corresponding to the type of the
  term). The <verbatim|Core.eval> function performs this interpretation by
  recursively evaluating the interpretation of the core Simplicity
  combinators from the algebra.

  What sort of Simplicity algebras are there? The most obvious one is the
  functional semantics of Simplicity. The domain of this algebra is the
  functions between Simplicity types. This domain is indexed by the input and
  output Simplicity types. The interpretation of the <math|<math-ss|iden>>
  and <math|<math-ss|unit>> constants are the idenity and constant-unit
  functions respectively and the intepretation of the other core Simplicity
  combinators is also in accordance with Simplicity's denotational semantics.
  This algebra is defined in the <verbatim|CoreSem> structure and the
  <verbatim|CorSem_correct> lemma proves that the interpretation of terms in
  the ``initial'' representation into this algebra results in the same
  function that the <verbatim|eval> function from
  <verbatim|Simplicity/Core.v> produces. The <verbatim|\|[x]\|> notation
  denotes this denotation semantics using the <verbatim|CoreSem> domain.

  Another example of a Simplicity algebra is the ``initial'' reprsentation of
  terms themselves, which form a trivial algebra. This domain of Simplicity
  terms is also indexed by input and output Simplicity types and the
  constants and combinators are interpreted as themselves. This algebra is
  defined in the <verbatim|Core.Term> structure and the
  <verbatim|Core.eval_Term> lemma proves that the interpretation of any term
  in this algebra returns the original term back.

  There are several other Simplicity algebras. Programs for the Bit Machine
  form a Simplicity algebra with the translation from Simplicity to Bit
  Machine code defining the interpreptation of core Simplicity combinators.
  Also 256-bit hashes are a Simplicity algebra with the merkle root
  computation defining the interpretation of core Simplicity combinators.
  Static analysis of resource usage for Simplicity expressions will for yet
  another set of Simplicity algebras.

  Instances of Simplicity algebras are declared as <verbatim|Canonical
  Structures>. \ This allows Coq's type inference engine to infer the
  interpration of Simplicity terms when they are used in the typing contexts
  of domain of one of these Simplicity algebras.

  <subsubsection|The ``Final'' Representation>

  The ``final'' representation of a Simplicity term is as a function that
  selects a value out of any Simplicity algebra and does so in a ``uniform''
  manner. A ``uniform'' manner means a function that satifies the
  <verbatim|Core.Parametric> property which effectively says that that the
  values choosen by the function from two domains must each be constructed
  from a composition of the intepretation of combinators in the two domains
  in the same way. In other words, the function must act the the
  intepretation of some ``inital'' represented term under
  <verbatim|Core.eval> for any domain.

  Terms in the ``inital'' representation can be converted to the ``final''
  representation by parital application of <verbatim|Core.eval>. The
  <verbatim|Core.eval_Parametric> lemma proves that the resulting ``final''
  representation resulting from <verbatim|Core.eval> satisfies the
  <verbatim|Core.Parametric> property.

  Terms in the ``final'' representation can be converted into the ``initial''
  representation by applying the function to the <verbatim|Core.Term>
  Simplicity algebra. The <verbatim|Core.eval_Term> lemma shows that
  converting from the ``initial'' representation to the ``final''
  representation and back to the ``initial'' representation returns the
  original value. The <verbatim|Core.term_eval> lemma shows that starting
  from any term in the ``final'' representation that satsifies the
  <verbatim|Core.Parametric> property and converting it to the ``initial''
  representation and back to the ``final'' representation results in an
  equivalent term. This completes the proof at the two representations are
  isomorphic.

  <subsubsection|Constructing ``Final'' Terms>

  To faciliate the construction of expression in the ``final''
  representaiton, the nine core combinators are defined as functions
  parameterized over all Simplicity algebras, and each combinator is proven
  to be parameteric or to preserve parametericity. For the most part, these
  combinators can be used to write Simplicity expressions in the ``final''
  representation in the same way one would use constructors to write
  Simplicity expressions in the ``initial'' representation. On top of this,
  notation <verbatim|s &&& t> is defined for the pair combinator, and
  <verbatim|s \<gtr\>\<gtr\>\<gtr\> t> is defined for the composition
  combinator. Also the <verbatim|'H'>, <verbatim|'O'>, and <verbatim|'I'>
  notations for sequences of takes and drops over the identity combinator is
  also defined.

  For every expression built in the ``final'' representation, it is necessary
  to prove that the result sastifies the paramatricity property. A
  <verbatim|parametricity> hint database is provided to faciliate automatic
  proofs of these results. Users should add their own parametricity lemmas to
  the hint database as they create new Simplicity expressions. Some examples
  of this can be found in the <verbatim|Simplicity/Arith.v> module.

  <subsection|Why two representations of Terms?>

  The ``initial'' inductive representation is the traditional definition one
  expects for terms and is easy to reason inductively about. This is the
  representation we will typically use in proofs. The problem with this
  representation is that, due to lack of sharing between sub-expressions, it
  is expensive to evaluate with these terms inside Coq itself. For example,
  one cannot compute Merkle roots of anything but the most trivial of
  expressions.

  The ``final'' algebra representation solves this problem by allowing
  transparent sharing of expressions. In the ``final'' representation, terms
  are really values of a Simplicity algebra. When these values are shared
  using in Coq's let expressions, or shared via some function argument in
  Coq, those values of the algebra are shared during computation within Coq.
  This representation makes it feasable to acutally compute Merkle roots for
  Simplicity expressions directly inside Coq.

  Both representations are used throughout the Simplicity Coq library. The
  ``final'' representation is used when building concrete Simplicity
  expressions. The ``initial'' representation is used when reasoning about
  functions of Simplicity expressions. The isomorphism between the two
  representations is used to transport theorems between them.

  You will find that I typically use <verbatim|term : Core.Algebra> as the
  variable name for an abstract Simplicity algebra. I use this variable name
  because <verbatim|Core.Term> are the most generic type of Simplicity
  algebra (formally knowns as an initial algebra) so it makes sense to think
  of generic Simplicity algebras as if they are term algebras.

  <section|Example Simplicity Expressions>

  <subsection|Bits>

  The <verbatim|Simplicity/Bit.v> file defines notation for the Simplicity
  type for bits, and notation for their two values <verbatim|'Bit.zero'> and
  <verbatim|'Bit.one'>. The Simplicity expressions <verbatim|false> and
  <verbatim|true> are defined to be the constant functions that return the
  zero and one bit respectively. A few logical combinators are defined for
  bits, including the <verbatim|cond <em|thn> <em|els>> combinator which does
  case analysis on one bit of input, and executes <verbatim|<em|thn>> or
  <verbatim|<em|els>> expressions according to whether the bit represented
  true or false.

  All the combinators and Simplicity expressions are given in the ``final''
  representation and parametricity lemmas are provided.

  <subsection|Arithmetic>

  The <verbatim|Simplicity/Arith.v> file defines types for multi-bit words
  and defines Simplicity expressions for addition and multiplication on those
  words. <verbatim|Word <em|n>> is a Simplicity type of a
  <math|2<rsup|n>>-bit word. The <verbatim|ToZ> module defines a class of
  types of finite words. The class provides <verbatim|toZ> and
  <verbatim|fromZ> operations that convert between standard Coq integers and
  these types of finite words along with proofs that the conversion functions
  are inverses modulo the word size. <verbatim|Canonical Structure>
  declarations provide implementations for the <verbatim|Bit> and
  <verbatim|Word <em|n>> types and for pairs of of such types.

  The <verbatim|Simplicity/Arith.v> file also defines the following
  Simplicity expressions:

  <\itemize-dot>
    <item><verbatim|adder : forall n term, term (Word n * Word n) (Bit * Word
    n)>

    <item><verbatim|fullAdder : forall n term, term ((Word n * Word n) * Bit)
    (Bit * Word n)>

    <item><verbatim|multiplier : forall n term, term (Word n * Word n) (Word
    (S n))>

    <item><verbatim|fullMultiplier : forall n term,<next-line>term ((Word n *
    Word n) * (Word n * Word n)) (Word (S n))>\ 
  </itemize-dot>

  The <verbatim|adder> expression defines the sum of two <math|2<rsup|n>>-bit
  word, returning a carry bit and a <math|2<rsup|n>>-bit word result. The
  <verbatim|fullAdder> expression defines the sum of two <math|2<rsup|n>>-bit
  word and one (carry input) bit, returning a carry bit and a
  <math|2<rsup|n>>-bit word result. The <verbatim|multiplier> expression
  defines the product of two <math|2<rsup|n>>-bit word and returns a
  <math|2<rsup|n+1>>-bit word. The <verbatim|fullMultiplier> expression takes
  a quadruple, <math|<around*|(|<around*|(|a,b|)>,<around*|(|c,d|)>|)>> of
  <math|2<rsup|n>>-bit words and returns <math|a\<cdot\>b+c+d> as a
  <math|2<rsup|n+1>>-bit word.

  Each of these expressions has an associated correctness lemma. These
  expressions are all defined in the ``final'' representation and there are
  parametricity lemmas for each expression.

  <subsection|SHA256>

  <section|The Hierarchy of Simplicity Language Extensions>

  <big-figure|<image|inheritance.Coq.eps||8cm||>|The inheritance hierarchy of
  algebras for Simplicity's languge extensions in
  Coq.<label|fig:inheritance>>

  So far we've only covered the algebra for the Core Simplicity language in
  Coq. \ The various extensions to this Core Simplicity language are captured
  by extensions to the record type for the Core Simplicity algebra.
  Figure<nbsp><reference|fig:inheritance> illustrates the names of the
  algebras extending the <verbatim|Core> language algebra and their
  inhieritance relationship. \ We use the ``packed-classes'' method for
  formalzing the inheritance releation of these extensions in Coq. Readers
  unfamiliar with this style should first read ``<hlink|Canonical Structures
  for the working Coq user|https://hal.inria.fr/hal-00816703v1/document>''<inactive|<cite|<with|color|red|TODO>>>
  and ``<hlink|Packaging Mathematical Structures|https://hal.inria.fr/inria-00368403v1/document>''<inactive|<cite|<with|color|red|TODO>>>.

  Roughly speaking, there are two dimensions to the inheritence structure.
  \ In one direction, the <verbatim|Core>, <verbatim|Witness>, and
  <verbatim|Delegation> algebras all have semantics that can be intepreted as
  pure functions. \ That is, the function semantics of terms from these
  languages can be evaluated as functions that have no side-effects and can
  return values within any monad, including the identity monad.

  The next layer in this direction, <verbatim|Assertion>,
  <verbatim|AssertionWitness>, and <verbatim|AssertionDelegation>, extend the
  previous layer with assertion and failure expressions. \ These expressions
  introduce the failure effect and the functional semantics of terms from
  these languages return values within a <verbatim|MonadZero>, which includes
  the <verbatim|option> monad.

  The last layer in this direction, <verbatim|Primitive>, <verbatim|Jet>,
  <verbatim|FullSimplicity>, and <verbatim|FullSimplicityWithDelegation>,
  include primitive terms that are particular to the specific blockchain
  application. \ The functional semantics of terms from these language return
  values within a monad that caputures the particular effects of the
  blockchain application. \ In the case of Bitcoin, the effects are captured
  by an environment (a.k.a reader) monad that provides read-only access to
  the signed transaction data.

  We break up the langauge of Simplicity into these layers because it helps
  us isolate the side-effects of the various language extensions when
  reasoning about Simplicity programs. \ When dealing with a sub-expression
  from the first layer, one can safely ignore the enviroment and failure
  effects and reason only about pure functions. Afterwards, various lemmas,
  such as <code|<code*|Simplicity.Alg.CoreSem_initial>> or
  <verbatim|Simplicity.Alg.AssertionSem_initial>, can be used to lift results
  into the monads use by the other layers when combining the pure
  sub-expression with other sub-expressions that do have effects.

  The other dimension of the inheritence structure breaks the language into
  feature sets. \ The <verbatim|Core>, <verbatim|Assertion>, and
  <verbatim|Primitive> algebras exclude witness and delegation features and
  encompse the set of language features that <verbatim|Jet>s are restricted
  to using. \ The next layer, <verbatim|Witness>,
  <verbatim|AssertionWitness,> and <verbatim|FullSimplicity>, add witness
  features cumulating in the <verbatim|FullSimplcity> algebra defining the
  Full Simplicity language. \ The last layer, <verbatim|Delegation>,
  <verbatim|AssertionDelegation>, and <verbatim|FullSimplicityWithDelgation>
  provides the powerful and dangerous delegation extension, which should only
  be used with caution.

  We cover these language extensions in more detail below.

  <subsection|Witness>

  The <verbatim|Witness> algebra, found in <verbatim|Simplicity/Alg.v>,
  \ extends the <verbatim|Core> algebra with the <verbatim|witness>
  combinator. The <verbatim|WitnessFunSem> and <verbatim|WitnessSem>
  canonical structures define the function semantics by interpreting the
  terms as pure functions and as Kleisli morphisms for any monad,
  respectively. \ The <verbatim|Witness_initial> lemma relates these two
  intepretations.

  <subsection|Assertion>

  The <verbatim|Assertion> algebra, found in <verbatim|Simplicity/Alg.v>,
  extends the <verbatim|Core> algebra with the <verbatim|assertl>,
  <verbatim|assertr>, and <verbatim|fail> combinators. \ The
  <verbatim|AssertionSem> canonical structure defines the functional
  semantics of Simplicity with assertions by interpreting terms as Kleisli
  morphisms for a monad with zero. The <verbatim|AssertionSem_initial> lemma
  shows that when reasoning about the function semantics of Simplicity with
  assertions, it suffices to reason within the <verbatim|option> monad and
  translate the result to any other monad with zero via the
  <verbatim|optionZero> homomorphism.

  The <verbatim|AssertionWitness> algebra is simply the meet of the
  <verbatim|Assertion> and <verbatim|Witness> algebras without adding any new
  combinators.

  <subsection|Delegation>

  The <verbatim|Delegation> algebra, found in
  <verbatim|Simplicity/Delegation.v>, extends the <verbatim|Witness> algebra
  with the <verbatim|disconnect> combinator. The
  <verbatim|AssertionDelegation> algebra is simply the meet of the
  <verbatim|Assertion> and <verbatim|Delegation> algebras (equiv. the meet of
  the <verbatim|AssertionWitness> and <verbatim|Delegation> algebras) without
  adding any new combinators.

  \ Building the functional semantics of Simplicity with delegation involves
  a simultaneous computation of commitment merkle roots (see
  Section<nbsp><reference|SS:Coq:MerkleRoots>) and the functiona semantics.
  \ To support this the <verbatim|Delegator arr A B> type is the product of
  the <verbatim|arr A B> and the <verbatim|CommitmentRoot A B> types.
  \ Whenever <verbatim|arr> forms an algebra from any of the previous
  Simplicity language algberas, then \ <verbatim|Delegator arr> is also a
  member of the same algebra. \ Furtheremove whenver <verbatim|arr> is a
  Simplicity with witnesses algebra, then \ <verbatim|Delegator arr> is a
  Simplicity with witnesses and delegation algebra. \ Similarly whenver
  <verbatim|arr> is a Simplicity with assertions and witnesses algebra, then
  \ <verbatim|Delegator arr> is a Simplicity with assertions, witnesses and
  delegation algebra.

  The <verbatim|runDelegator> projeciton extract <verbatim|arr A B>, from
  <verbatim|Delegator arr A B>. \ For example, <verbatim|Arrow A B> is a
  functional semantics for Simplicity with witnesses. \ Then, when
  <verbatim|<em|t>> is a term for Simplicity with witneses and delegation,
  <verbatim|runDelegator t : Arrow A B> is the functional semantics of
  <verbatim|<em|t>>.

  The <verbatim|runDelegator_correctness> lemma shows that for Simplicity
  terms that don't have delegation, then <verbatim|runDelegator> returns the
  original semantics.

  <subsection|Primitives>

  The Simplicity language is parameterized by the choice of
  blockchain-specific primitives. \ Currently we use Coq's module system to
  capture this parameterizatin. \ A <verbatim|Module Type PrimitiveSig> found
  in <verbatim|Simplicity/Primitive.v> defines the parameters that define
  these blockchain-specific applications of simplicity:

  <\itemize>
    <item>A type family <verbatim|t : Ty -\<gtr\> Ty -\<gtr\> Set> of the
    primitive expression's syntax.

    <item>A function <verbatim|tag : forall A B, t A B -\<gtr\> hash256> that
    defines the Merkle roots for the primitives.

    <item>A type \ <verbatim|env : Set> that captures the relevent read-only
    context used to intepret the primitives.

    <item>A function <verbatim|sem : forall A B, t A B -\<gtr\> A -\<gtr\>
    env -\<gtr\> option B> that defines the functional semantics of the
    primtives.
  </itemize>

  At the moment, this frameworks only supports primitives that use the
  enviroment (and failure) side-effect; however this framework could be
  extended to allow primtives that require other effects that can be captured
  by commutative and idemponent monads (for example, the writer effect for a
  commutative and idempontent monoid).

  Given an instance of the <verbatim|PrimitiveSig>'s parameters, the
  <verbatim|PrimitiveModule> defines the algebras for the parts of the
  Simplicity langauge that depends on the primtives. \ This includes the
  <verbatim|Primitive>, <verbatim|Jet>, <verbatim|FullSimplicity> and
  <verbatim|FullSimplicityWithDelegation> algebras.

  The <verbatim|Primitive> algebra extends the <verbatim|Assertion> algebra
  with the primitives given by the <verbatim|PrimitiveSig>'s type family
  <verbatim|t> through the <verbatim|prim> combinator. \ The
  <verbatim|primSem M> arrow is the Kleisli arrow for the monad generated by
  adding an environment effect for the <verbatim|PrimitiveSig>'s
  <verbatim|env> to the monad <verbatim|M>. \ The <verbatim|PrimitivePrimSem>
  canonical structure provides the funciton semantics for Simplicity with
  primitives by interpreting terms as <verbatim|primSem M> whenever
  <verbatim|M> is a monad zero.

  <subsubsection|Bitcoin>

  The <verbatim|Bitcoin> module found in <verbatim|Simplicity/Primitive/Bitcoin.v>
  provides these an instance of the <verbatim|PrimitiveSig> parameters used
  for a Bitcoin or Bitcoin-like applicaiton of Simplicity. \ The structures
  defining the signed transaction data are specified cumulating in the
  <verbatim|sigTx> data type.

  The <verbatim|Bitcoin.prim> type lists the typed primitive expressions
  defined in Section<nbsp><reference|ss:BitcoinTransactions>. \ The
  <verbatim|environment> type captures the read-only context for interpreting
  these primitives and it includes a <verbatim|sigTx>, the index withing this
  transaction that is under consideration, and the commitment Merkle root of
  the script being evaluated.

  Lastly, the <verbatim|sem> function defines the functional semantics of the
  primitives in accordance with Section<nbsp><reference|ss:BTDenotationalSemantics>
  and the <verbatim|tag> function defines the merkle roots for the primitives
  in accordance with Section<nbsp><reference|ss:BTMerkleRoots>. We use
  <verbatim|vm_compute> in the defintion of <verbatim|tag> to pre-evaluate
  the definitions of the merkle roots as an optimization.

  <subsection|Jets>

  The <verbatim|Jet> algebra, found in the <verbatim|PrimitiveModule> in
  <verbatim|Simplicity/Primtive.v>, extends the <verbatim|Primitive> algebra
  with generic support for jets. The <verbatim|jet> combinator takes a term
  <verbatim|<em|t>> from the <verbatim|Primitive> algebra and the
  <verbatim|JetPrimSem> canonical structures defines the functional semantics
  of a jet to be the function sematics of <verbatim|<em|t>>. Operationaly, we
  expect implementations of specific jets to be natively implemented, but
  this detail goes beyond the scope of the specification of Simplicity within
  Coq.

  Because <verbatim|<em|t>> is restricted to being a term from the
  <verbatim|Primitive> algebra, jets cannot contain <verbatim|witness> or
  <verbatim|disconnect> sub-expressions. \ While our generic definiton of
  <verbatim|jets> allows any term from the <verbatim|Primtiive> algebra to be
  a jet, we expect specific applications of Simplicity to limit themselves to
  a finite collection of jets through its serialization format.

  <subsection|Full Simplicity>

  The <verbatim|FullSimplicity> algebra, found in the
  <verbatim|PrimitiveModule> in <verbatim|Simplicity/Primtive.v>, is the meet
  of the <verbatim|Jet> and the <verbatim|Witness> algebras (equiv. the meet
  of the <verbatim|Jet> and <verbatim|AssertionWitness> algebras) with no
  additonal combinators. \ It defines the full Simplicity language. \ The
  <verbatim|SimplicityPrimSem> canonical structure provides the functional
  semantics of the full Simplicity langauge as the <verbatim|primSem M> type
  familiy when <verbatim|M> is a monad zero.\ 

  The <verbatim|FullSimplicityWithDelegation> algebra is the the meet of the
  <verbatim|Jet> and the <verbatim|Delegation> algebras (equiv. the meet of
  the <verbatim|FullSimplicity> and <verbatim|Delegation> algebras, or the
  meet of the <verbatim|FullSimplicity> and <verbatim|AssertionDelegation>
  algebras, etc.) defines the full Simplicity with delegation langauge. \ The
  functional semantics are defined via the
  <verbatim|SimplicityDelegationDelegator> canonical structure whose domain
  includes <verbatim|Delegator (primSem M)> when <verbatim|M> is a monad
  zero. \ Using <verbatim|runDelegator>, one can extract a <verbatim|primSem
  M> value as the functional semantics.

  <section|Merkle Roots><label|SS:Coq:MerkleRoots>

  The <verbatim|Simplicity/MerkleRoot.v> file defines a Merkle root of types,
  and the commitment Merkle root and witness Merkle roots for part of the
  Simplicity langauge. \ The Merkle root of types is specified by
  <verbatim|><code|<code*|typeRootAlg>> and defined by <verbatim|typeRoot>.
  \ The in the <verbatim|CommitmentRoot A B> family the parameters are
  phantom parameters, and the value is always a <verbatim|has256> type.
  \ Canonical Structures provide instances of <verbatim|CommitmentRoot> for
  Core Simplicity, and Simplicity with assertions and witnesses. \ The
  <verbatim|CommitmentRoot> for delegation is found in
  <verbatim|Simplicity/Delegation.v> and the <verbatim|CommitmentRoot> for
  primitives, jets, Full Simplicity and Full Simplicity with delegation is
  found in <verbatim|Simplicity/Primtive.v>.

  These Merkle roots are computed using the SHA-256 compression function with
  unique tags providing the initial value for each language contstruct.
  \ These tags are in turn the SHA-256 hash of short (less than 56 character)
  ASCII strings. \ The Coq definition of SHA-256 is taken from the VST
  (Verified Software Toolchain) project<inactive|<cite|<with|color|red|TODO>>>
  and the <verbatim|Simplicity/Digest.v> module provides an interface to that
  project.

  The VST implemention of SHA-256 is effecent enough that it is practical to
  compute some commitment Merkle roots of functions inside Coq itself using
  <verbatim|vm_compute>. \ See <verbatim|Fact Hash256_hashBlock> at the end
  of <verbatim|Simplicity/SHA256.v> for an example of comuting the commitment
  Merkle root of a Simplicity function that computes the SHA-256 compression
  function.

  <section|The Bit Machine>

  The <verbatim|Simplicity/BitMachine.v> file provides the primary definition
  of the abstract Bit Machine. This definition, and hence this file, is
  independent of the rest of the Simplicity language.

  The <verbatim|Cell> type explicity tracks cell values in the bit machien as
  being one of <verbatim|0>, <verbatim|1>, and undefined. <verbatim|None>
  represents the undefined value and <verbatim|Some false> and <verbatim|Some
  true> represent <verbatim|0> and <verbatim|1> respectively.

  The <verbatim|ReadFrame> record represents read frames. It uses a zipper
  representation of a list with a cursor: The elements of the list in front
  of the cursor are in the <verbatim|nextData> field and the elements of the
  list behind the cursor are in the <verbatim|prevData> field stored in
  <em|reverse order>. The <verbatim|setFrame> function builds a read frame
  from a list with the cursor set to the beginning of the frame.

  The <verbatim|WriteFrame> record represents write frames. It uses a similar
  zipper representation where the <verbatim|writeData> field holds the
  elements behind the cursor in <em|reverse order>. Because write frames are
  append only, every cell in front of the cursor must be an undefined value.
  For this reason we only store the number of cells in front of the cursor in
  the <verbatim|writeEmpty> field. The <verbatim|newWriteFrame> function
  builds an empty write frame of a given size and the
  <verbatim|fullWriteFrame> function builds an filled write frame from a
  list.

  The <verbatim|RunState> record represents the non-halted states of the Bit
  Machine. It consists of

  <\itemize-dot>
    <item><verbatim|inactiveReadFrames>: a list of inactive read frames, with
    the bottom of the stack at the end of the list.

    <item><verbatim|activeReadFrame>: the active read frame, which is the top
    value of the non-empty stack of read frames.

    <item><verbatim|activeWriteFrame>: the active write frame, which is the
    top value of the non-empty stack of write frames.

    <item><verbatim|inactiveWriteFrames>: a list of inactive write frames,
    with the bottom of the stack at the end of the list.
  </itemize-dot>

  The <verbatim|State> variant is either a <verbatim|RunState> or the
  <verbatim|Halted> state and represents the possible states of the Bit
  Machine. We make the injection of <verbatim|RunState> into <verbatim|State>
  a coercion.

  It is sometimes useful to decompose the Bit Machine's state as\ 

  <\equation*>
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n<rsub|0>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><cearr|c<rsub|1>\<cdots\>c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  where we are locally interested in what is immediately in front of the
  active read frame's cursor, <math|<carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n<rsub|0>>>>,
  and what is immediately surrounding the active write frame's cursor,
  <math|<cearr|c<rsub|1>\<cdots\>c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>>>.
  This is captured by the <verbatim|LocalState> type, noting that the data
  immediately surrounding the active write frame's cursor is captured by the
  <verbatim|WriteFrame> type. The remainder of the state, consisting of
  <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|>\<bullet\>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\>\<bullet\>\<cdummy\><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
  is captured by the <verbatim|Context> type, which happens to be isomorphic
  to the <verbatim|RunState> type. The <verbatim|fillContext> function
  combines a <verbatim|Context> value and a <verbatim|LocalState> value to
  build a complete <verbatim|RunState> value.

  Sometimes we are intersted in of some <verbatim|LocalState> within another
  <verbatim|LocalState>. The context of such a decomposition is isomorphic to
  <verbatim|LocalState> and we don't even both giving a type alias to this.
  The <verbatim|appendLocalState> funciton combines a context,
  <verbatim|ls1>, with a <verbatim|LocalState>, <verbatim|ls2>, to build a
  combined <verbatim|LocalState>. <verbatim|appendLocalState> makes
  <verbatim|<verbatim|LocalState>> into a monoid and <verbatim|fillContext>
  becomes a monoid action on <verbatim|Context>s with respect to this monoid.
  This theory isn't fully developed in Coq, but will be if it is needed. The
  <verbatim|context_action> lemma proves the monoid action property, which is
  the only theorem developed so far.

  The <verbatim|StateShape> type is constructed using similar fields as the
  <verbatim|State> type and contains a sequence of numbers. This is used for
  counting the number of cells in the various components of the Bit Machine's
  <verbatim|State>. The <verbatim|stateShapeSize> function tallies up the
  totals and is used later in the <verbatim|maximumMemoryResidence> function.

  <subsection|Bit Machine Code>

  The <verbatim|MachineCode.T <em|S1> <em|S2>> type enumerates the nine basic
  instructions of the Bit Machine. The type of these instructions are
  parameterized by the legal states that the instructions can successfully
  operate in, <verbatim|<em|S1>>, and the resulting state after execution of
  the instruction, <verbatim|<em|S2>>. In this way, the
  <verbatim|MachineCode.T> type family represents a precategory (also known
  as a directed multi-graph) that captures the machine instructions and their
  semantics. There is an objects (a.k.a. nodes) for every possible state of
  the Bit Machine. There is an arrow (a.k.a. edge) between two states if
  there is an instruction of the Bit Machine that successfully transitions
  from the source state to the target state, and that arrow (a.k.a. edge) is
  labled with the name of the instruction. The <verbatim|Abort> instruction
  is the only instruction whose final state is the <verbatim|Halted> state.
  No instruction begins from the <verbatim|Halted> state. The specific type
  <verbatim|MachineCode.T <em|S1> <em|S2>> is the type of all instructions
  that transition from state <verbatim|<em|S1>> to state <verbatim|<em|S2>>.

  A thrist of <verbatim|MachineCode.T> is the free category generated from
  the precategory <verbatim|MachineCode.T>. This free category can also be
  understood as a collection of all paths through the directed graph of all
  machine instructions and their associated state transitions. The specific
  type <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> is the type of all
  sequences of instructions that transition from state <verbatim|<em|S1>> to
  state <verbatim|<em|S2>>. This type captures the semantics of sequences of
  machine instructions.

  The notation <verbatim|<em|S1> ~~\<gtr\> <em|S2>> denotes the
  <verbatim|MachineCode.T <em|S1> <em|S2>> type of single step transitions,
  which corresponds to <math|S<rsub|1>\<rightsquigarrow\>S<rsub|2>>. The
  notation <verbatim|<em|S1> -\<gtr\>\<gtr\> <em|S2>> denotes the
  <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> type of multi-step
  (including 0 steps) transitions between states <verbatim|<em|S1>> and
  <verbatim|S2> and the trace of the instructions used. The
  <verbatim|runHalt> lemma proves that the only trace that begins from the
  <verbatim|Halted> state is the empty trace.

  <subsubsection|Bit Machine Programs>

  We interpret a Bit Machine <verbatim|Program> as a function taking an
  initial machine state and, if successful, returning a final machine state
  along with a thrist of machine instructions that connect the initial state
  to the final state. The notation <verbatim|S1 \<gtr\>\<gtr\>- k
  -\<gtr\>\<gtr\> S2> corresponds to <prog|S<rsub|1>|k|S<rsub|2>> and denotes
  that the program <verbatim|k> when started in state <verbatim|S1>
  successfully executes and ends in state <verbatim|S2>. The <verbatim|trace>
  function extracts a <verbatim|S1 -\<gtr\>\<gtr\> S2> trace from a program
  <verbatim|k> when <verbatim|S1 \<gtr\>\<gtr\>- k -\<gtr\>\<gtr\> S2> holds.

  For each machine instruction, we use <verbatim|makeProgram> to define a
  single instruction <verbatim|Program> that tries to execute that single
  instruction once and returns that state transition. If the initial
  non-halted state given to these single instruction programs isn't valid for
  their instruction, the program fails by returning <verbatim|None>. However,
  when the initial state is the <verbatim|Halted> state, the program succeeds
  but ignores its instruction and remains in the <verbatim|Halted> state.
  This corresponds to the <prog|<halted>|i|<halted>> deduction. These single
  instruction programs have an associated correctness lemma that proves they
  run successfully when run from an initial state valid for their instruction
  and a completeness lemma that proves that they were run from either a valid
  initial state or the <verbatim|Halted> state. We also define the trivial
  <verbatim|nop> program that contains no instructions and always succeeds.

  These single instruction programs can be combined into more complex
  programs using the <verbatim|seq> and <verbatim|choice> combinators. The
  <verbatim|seq> combinator sequences two programs, running the second
  program starting from the final state of the first program and combines
  their thrists. The sequence fails if either program fails. The
  <verbatim|choice> combinator picks between running two programs by peeking
  at the cell under the active read frame's cursor from the initial state and
  running either the first or second program depending on whether the cell
  holds a <verbatim|0> or <verbatim|1> value. When starting from a non-halted
  state, if the cell holds an undefined value, or if the active read frame's
  cursor is at the end of the frame, the <verbatim|choice> combinator fails.
  When started from the <verbatim|Halted> state, the <verbatim|choice>
  program succeeds but remains in the <verbatim|Halted> state.

  The notations <verbatim|<em|k0> ;;; <em|k1>> and <verbatim|<em|k0> \|\|\|
  <em|k1>> denote the sequence and choice combinations respectively of two
  programs and correspond to <math|k<rsub|0>;k<rsub|1>> and
  <math|k<rsub|0><around*|\|||\|>k<rsub|1>>. We also define the combinator
  <verbatim|bump <em|n> <em|k>> which corresponds to <math|n\<star\>k>.

  The <verbatim|runMachine> function takes a <verbatim|Program> and an
  initial <verbatim|State> and extracts the resulting final <verbatim|State>
  and the trace to get there, if the program is sucessful. For denotational
  semantics we only care about the resulting final state. For operational
  semantics we will care how we got there. A few lemmas are provided to help
  reason about the behaviour of <verbatim|runMachine> when running the
  program combinators.

  The <verbatim|maximumMemoryResidence> function computes the maximum number
  of cells used by any intermediate state from the trace of execution of a
  Bit Machine program. A few lemmas are provided to help reason about the
  behaviour of <verbatim|maximumMemoryResidence> when running the program
  combinators.

  <subsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Simplicity/Translate.v> file defines how to transform
  Simplicity programs into Bit Machine programs that perform the same
  computation. The <verbatim|bitSize> and <verbatim|encode> functions
  implement <math|bitSize<around*|(|A|)>> and <math|<rep|a|A>> respectively.

  The <verbatim|Naive.translate> structure provides a Simplicity algebra for
  Bit Machine <verbatim|Progam>s that interprets Simplicity terms according
  to the naive translation. The <verbatim|Naive.translate_correct> theorem
  proves that the <verbatim|Program> generated by <verbatim|Naive.translate>
  when started from a state that contains an encoding of Simplicity
  function's input successfuly end up in a final machine state that contains
  an encoding of Simplicity function's output (and input). The
  <verbatim|spec> property defines an inductive hypothesis that is used by
  <verbatim|Naive.translate_spec> that makes up the heart of this proof.

  The <verbatim|Naive.translate_correct_parametric> theorem is a variation of
  the <verbatim|Naive.translate_correct> theorem. The
  <verbatim|Naive.translate_correct> operates on Simplicity term in the
  ``initial'' representaiton whereas the <verbatim|Naive.translate_correct_parametric>
  theorem operates on Simplicity terms in the ``final'' representation.

  <subsection|Static Analysis>

  The <verbatim|Simplicity/StaticAnalysis.v> files defines the static
  analyses of Simplicity program that compute bounds on the various
  computational resources used by the Bit Machine when executing translated
  Simplicity. The file also proves the correctness of these upper bounds.

  The <verbatim|MaximumMemory> module defines the
  <verbatim|MaximumMemory.extraMemoryBound> algebra which is used to compute
  an upper bound on additional memory that will be used when Simplicity
  sub-expressions are naively translated to the Bit Machine and executed. The
  <verbatim|MaximumMemory.Core_spec> lemma proves that for naively translated
  core Simplicity expressions, the maximum memory used by the Bit Machine is
  the memory needed by the size of the initial state, plus the results of
  <verbatim|MaximumMemory.extraMemoryBound>. This bound holds no matter what
  the starting state is, even if it is not a valid state for holding the
  input for the Simplicity expression.

  The <verbatim|MaximumMemory.CellBound> function computes the memory used by
  the Bit Machine for evaluating Simplicity expressions starting from a
  standard initial state and <verbatim|MaximumMemory.CellBound_correct>
  proves that this upper bound is correct.

  <chapter|Haskell Library Guide>

  WARNING: None of the Haskell library development is normative. There is no
  formalized connecton between any of the Haskell library and Simplicity's
  formal semantics and development in Coq. There could be errors in the
  Haskell library that cause it to disagree with the formal development
  defined in Coq. This library is intended to be used for experimental,
  exporitory and rapid development of Simplicity related work, but should not
  be relied upon for production development. For production development,
  formal developments in Coq should be done.

  The Haskell development for Simplicity is found in the <verbatim|Haskell>
  directory. The <verbatim|Haskell/Tests.hs> file imports the various test
  modules throught the development to build a testing executable to run them
  all.

  <section|Simplicity Types>

  The <verbatim|Simplicity/Ty.hs> file contains the development of Simplicity
  types. There are three different ways that Simplicity types are captured in
  Haskell.

  The primary way Simplicity types are captured is by the <verbatim|TyC>
  class which only has instances for the Haskell types that correspond to the
  Simplicity types:

  <\itemize-dot>
    <item><verbatim|instance TyC ()>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (Either a b)>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (a, b)>
  </itemize-dot>

  The <verbatim|TyC> class is crafted so that is methods are not exported.
  This prevents anyone from adding further instances to the <verbatim|TyC>
  class.

  The second way Simplicity types are captured is by the <verbatim|TyReflect>
  GADT:

  <\code>
    data TyReflect a where

    \ \ OneR \ :: TyReflect ()

    \ \ SumR \ :: (TyC a, TyC b) =\<gtr\> TyReflect a -\<gtr\> TyReflect b
    -\<gtr\> TyReflect (Either a b)

    \ \ ProdR :: (TyC a, TyC b) =\<gtr\> TyReflect a -\<gtr\> TyReflect b
    -\<gtr\> TyReflect (a, b)\ 
  </code>

  This data type provides a concrete, value-level representation of
  Simplicity types that are tied to the type-level representation of types.
  For each Haskell type corresponding to a Simplicity type, <verbatim|a> the
  <verbatim|TyReflect a> type has exactly one value that is built up out of
  other values of type <verbatim|TyReflect> corresponding to the Simplicity
  type sub-expression. For example the value of type <verbatim|TyReflect
  (Either () ())> is <verbatim|SumR OneR OneR>.

  The <verbatim|reify :: TyC a =\<gtr\> TyReflect a> uses the one method of
  the <verbatim|TyC> class to produce the value of the <verbatim|TyReflect>
  GADT that corresponds to the type constrained by the <verbatim|TyC>
  constraint. When users have a Haskell type constrained by <verbatim|TyC>
  they can use <verbatim|reify> to get the corresponding concrete value of
  the <verbatim|TyReflect> GADT which can then be further processed. The
  <verbatim|reifyProxy> and <verbatim|reifyArrow> functions are helper
  functions for <verbatim|refiy> that let you pass types via a proxy.

  The third way Simplicity types are captured is by the <verbatim|Ty> type
  alias, which is the fixed point of the <verbatim|TyF> functor. This is a
  representation of Simplicity types as a data type. The <verbatim|one>,
  <verbatim|sum>, and <verbatim|prod> functions provide smart-constructors
  that handle the explicit fixpoint constructor. The <verbatim|memoCataTy>
  helps one build memoized functions that consume <verbatim|Ty> values.

  Generally speaking, we use <verbatim|TyC> to constrain Haskell types to
  Simplicity types when creating Simplicity expressions. This way Simplicty
  type errors are also Haskell type errors and can be caught by the Haskell
  compiler. We use the <verbatim|Ty> type when doing compuation like
  deserializing Simplicity expressions and performing unification for
  Simplicity's type inference. The <verbatim|TyReflect> GADT links these two
  representations. For example, the <verbatim|equalTyReflect> function can
  test if two Simplicity types are equal or not, and if they are equal then
  it can unify the Haskell type variables that represent the two Simplicity
  types. The <verbatim|unreflect> function turns a <verbatim|TyReflect> value
  into a <verbatim|Ty> value by forgetting about the type parameter.

  Within the <verbatim|Simplicity/Ty> directory, there are modules providing
  data types that are built from Simplicity types. The
  <verbatim|Simplicity/Ty/Bit.hs> module provides a <verbatim|Bit> type,
  corresponding to <math|<2>>, and the canonical isomorphism between
  Haskell's <verbatim|Bool> type and <verbatim|Bit>.

  The <verbatim|Simplicity/Ty/Word.hs> module provides the <verbatim|Word a>
  GADT that describes Simplicity types for multi-bit words. Its type
  parameter is restricted to either be a single <verbatim|Bit> word type or a
  product that doubles the size of a another word type. The
  <verbatim|wordSize> returns the number of bits a word has. The
  <verbatim|fromWord> and <verbatim|toWord> functions convert values of
  Simplicity words types to and from Haskell <verbatim|Integer>s (modulo the
  size of the word). The file also provides specializations of these various
  functions for popular word sizes between 8 and 256 bits.

  <section|Simplicity Terms>

  We do not provide a data type represenation of Simplicity terms. Instead
  terms are represented in tagless-final style<inactive|<cite|<with|color|red|TODO>>>.
  This style is analgous to the ``final'' represention of terms that is
  defined in the Coq library. The development of the term language for full
  Simplicity is split into two files.

  The <verbatim|Simplicity/Term/Core.hs> file develops the core Simplicity
  term langauge plus a few extensions. The <verbatim|Core> type class
  captures Simplicity algebras for core Simplicity expressions. Core
  Simplicity expressions are represented in Haskell by expressions of type
  <verbatim|Core term =\<gtr\> term a b> which are expressions that hold for
  all Simplicity algebras. Haskell's parametricity implicity implies the
  parametricity conditions that is explicitly required in the Coq
  development's ``final'' representation.

  This module provides infix operators, <verbatim|(\<gtr\>\<gtr\>\<gtr\>)>
  and <verbatim|(&&&)>, for the <verbatim|comp> and <verbatim|pair>
  Simplicity combinators respectively. It also provides notation for short
  sequences of string of <samp|I>'s, <samp|O>'s and <samp|H>'s. Note that
  because <verbatim|case> is a reserved word in Haskell we use
  <verbatim|match> for Simplicty's <samp|case> combinator. Examples of
  building Simplicity expressions can be found in the next section.

  This module also provides <verbatim|Assert>, <verbatim|Witness>, and
  <verbatim|Delegatate> classes for the failure, witness, and delgation
  language extensions respectively. Terms that make use of these extension
  will have these class contraints added to their type signatures. For
  example, a value of type <verbatim|(Core term, Witness term) =\<gtr\> term
  a b> is a term in the language of Simplicity with witnesses.

  This module provides <verbatim|(-\<gtr\>)> and <verbatim|Kleisli m>
  instances of these classes where possible that provide denotational
  semantics of core Simplicity and some extensions. For example, one can take
  core Simplicity terms and directly use them as functions. The semantics of
  <verbatim|Delegate> depends on the commitment Merkle root; you can find
  semantics for that extension in <verbatim|Simplicity/Semantics.hs> and it
  is discussed in Section<nbsp><reference|ss:DenotationalSemanticsOfFullSimplicity>.

  The <verbatim|Simplicity/Term.hs> module provides the blockchain primitives
  and jet extensions, in addition to re-exporting the
  <verbatim|Simplicity/Term/Core.hs> module. This separation lets
  <verbatim|Simplicity/Term/Core.hs> remain independent of the blockchain
  specific <verbatim|Simplicity/Primitive.hs> module. All the Simplicity
  extensions are gathered together in the <verbatim|Simplicity> class, whose
  associated values of type <verbatim|Simplicity term =\<gtr\> term a b> are
  terms in the full Simplicity language with delegation. The semantics of
  full Simplicity is discussed in Section<nbsp><reference|ss:DenotationalSemanticsOfFullSimplicity>.

  The primary purpose of using tagless-final style is to support transparent
  sharing of subexpressions in Simplicity. While subexpressions can be shared
  if we used a GADT to represent Simplicity terms, any recursive function
  that consumes such a GADT cannot take advantage of that sharing. Sharing
  results of static analysis between shared sub-experssions is critical to
  making static analysis practical. Adding explicit sharing to the Simplicity
  language would make the langauge more complex and would risk incorrectly
  implementing the sharing combinator. Explicitly building memoization tables
  could work, but will have overhead. For instance, we do do this for
  computing Merkle roots of Simplicity types. However, the solution of using
  tagless-final style lets us write terms in a natural manner and we get
  sharing for Simplicity expressions at exactly the points where we have
  sharing in the Haskell representation of the term.

  <section|Example Simplicity Expressions>

  The <verbatim|Simplicity/Programs> directory contains various developments
  of Simplicity expressions in Haskell. The
  <verbatim|Simplicity/Programs/Tests.hs> has some Quickcheck properties that
  provide randomized testing for some of the programs defined in this
  section.

  <subsection|Bits>

  The <verbatim|Simplicity/Programs/Bit.hs> file has Simplicity expressions
  for bit manipulation. <verbatim|false> and <verbatim|true> are Simplicity
  expressions for the constant functions of those types and <verbatim|cond>
  provides case analysis combinator for a single bit. There are combinators
  for various logical operators. These logical operators are short-circuted
  where possible. There are also a few trinary boolean Simplicity expressions
  that are used in hash functions such as SHA-256.

  <subsection|Multi-bit Words>

  The <verbatim|Simplicity/Programs/Word.hs> file provides support for
  multi-bit word expressions that operate on Simplicity's word types.

  \;

  <subsubsection|Arithmetic operations>

  The <verbatim|Simplicity/Programs/Word.hs> file provides the standard
  implemenations of the <verbatim|zero>, <verbatim|adder>,
  <verbatim|fullAdder>, <verbatim|multiplier>, and <verbatim|fullMultiplier>
  Simplicity expressions. Notice that the implementation of these functions
  is careful to use explicit sharing of Simplicity sub-expressions where
  possible through the <verbatim|where> clauses.

  <subsubsection|Bit-wise operations>

  The <verbatim|shift> and <verbatim|rotate> functions create Simplicity
  expressions that do right shifts and rotates of multi-bit words by any
  constant amount. Left (unsigned) shifts and rotates can be made by passing
  a negative value for the shift/rotate amount.

  The <verbatim|bitwise> combinator takes a Simplicity expression for a
  binary bit operation and lifts it to a Simplicity expression for a binary
  operation on arbitrary sized words that performs the bit operation
  bit-wise. There is also a variant, called <verbatim|bitwiseTri> the does
  the same thing for trinary bit operations.

  <subsection|Generic>

  The <verbatim|Simplicity/Programs/Generic.hs> file provides some Simplicity
  expressions that can apply to any Simplicity type.

  The <verbatim|scribe> function produces a Simplicity expression denoting a
  constant function for any value for any Simplicity type. The <verbatim|eq>
  Simplicity expression compares any two values of the same Simplicity type
  and deicides if they are equal or not.

  <subsection|SHA-256>

  The <verbatim|Simplicity/Programs/Sha256.hs> files provides Simplicity
  expressions to help compute SHA-256 hashes. The <verbatim|iv> Simplicity
  expression is a constant function the returns the initial value to begin a
  SHA-256 computation. The <verbatim|hashBlock> Simplicity expression
  computes the SHA-256 compression function on a single block of data. To
  compress multiple blocks, multiple calls to the <verbatim|hashBlock>
  function can be chained together.

  <section|Blockchain Primitives>

  We aim to keep the Haskell library of Simplicity modular over different
  blockchain applications. \ Different blockchain applications are provided
  in the <verbatim|Simplicity/Primitive> directory. \ At the moment only the
  Bitcoin blockchain applicaiton is provided by the
  <verbatim|Simplicity/Primitive/Bitcoin.hs>.

  The <verbatim|Simplicity/Primitive.hs> module provides an interface to the
  different possible primitives provided by different blockchain
  applications. \ This module exports

  <\itemize>
    <item><verbatim|Prim a b>, a GADT for different primitive expressions,
    <verbatim|>

    <item><verbatim|primPrefix> and <verbatim|primName> which are used to
    generate unique names for the Merkle roots of primtive expressions,

    <item><verbatim|PrimEnv> and <verbatim|primSem>, which provides the type
    of the context and the denotaitonal semantics for evaluating primitive
    expressions.
  </itemize>

  The library, by default, re-exports these values from the
  <verbatim|Simplicity/Primitive/Bitcoin.hs> module. For other blockchain
  applications, one can modify the file to re-export the other application's
  module for primitives. The Kleisli morphisms over a reader monad over
  <verbatim|PrimEnv> supports the semantics of primitive expressions.

  <subsection|Bitcoin Primitives>

  The <verbatim|Simplicity/Primitive/Bitcoin.hs> module provides the
  primitive expressions and their semantics for Simplicity's Bitcoin
  application. \ The <verbatim|Prim a b> GADT enumerates the list of
  primitive Simplicity expressions for Bitcoin. \ The <verbatim|PrimEnv>
  provides the context that a Simplicity expression is evaluated within,
  providing the signed transaction data, the index of the input being
  considered for redemption, and the commitment Merkle root of the Simplicity
  program itself. \ The <verbatim|primSem> function is an interpreter for
  these primitive expressions for the Bitcoin.

  The <verbatim|Simplicity/Primitive/Bitcoin/DataTypes.hs> module provides
  the data structures that make up the signed transaction data for Bitcoin.

  <section|Merkle Roots>

  The <verbatim|Simplicity/MerkleRoot.hs> module provides instances of
  Simplicity terms that compute the commitment and witness Merkle roots.
  \ The <verbatim|commitmentRoot> and <verbatim|witnessRoot> return these
  Merkle root values. The <verbatim|Simplicity/MerkleRoot.hs> module also
  provides a memoized computation of the Merkle roots for Simplicity types.

  The SHA-256 implemenation is provided through an abstract interface found
  in <verbatim|Simplicity/Digest.hs>.

  <section|Denotational Semantics of Full
  Simplicity><label|ss:DenotationalSemanticsOfFullSimplicity>

  The <verbatim|Simplicity/Term.hs> module provides <verbatim|(-\<gtr\>)> and
  <verbatim|Kleisli m> instances for the full Simplicity language excluding
  delegation. Semantics for the full Simplicity langauge with delegation,
  which depends on computing commitment Merkle roots, is found in the
  <verbatim|Simplicity/Semantics.hs> module.

  The <verbatim|Delegator p a b> helper type bundles a commitment Merkle root
  computation with the regular Simplicity semantics, allowing commitment
  Merkle roots and semantics to be evaluated concurrently. This allows us to
  create <verbatim|Delegate> and <verbatim|Simplicity> instances using
  <verbatim|Delegator>.

  The <verbatim|Semantics a b> is an instance of <verbatim|Delegator> for the
  Kleisli semantics that support the Blockchain primitives, and thus is an
  instance of the full Simplicity language with delegation. \ The
  <verbatim|sem> function unwraps all the type wrapers of <verbatim|Semantics
  a b> and provides a concrete function from <verbatim|PrimEnv> and
  <verbatim|a> to <verbatim|Maybe b>.

  <section|The Bit Machine>

  The <verbatim|Simplicity/BitMachine/> directory has modules related to the
  Bit Machine and evaluation of Simplicity via the Bit Machine.

  The <verbatim|Simplicity/BitMachine/Ty.hs> file defines <verbatim|bitSize>,
  <verbatim|padL>, and <verbatim|padR>, which define the <math|bitSize>,
  <math|padR> and <math|padL> functions from
  Section<nbsp><reference|ss:RepresentingValuesAsCellArrays>. They operate on
  the <verbatim|Ty> type. The file also defines variants of these three
  function that operate on the <verbatim|TyReflect> GADT instead.

  The <verbatim|Simplicity/BitMachine.hs> file (technically not in the
  <verbatim|Simplicity/BitMachine/> directory) defines the canonical type of
  a <verbatim|Cell> to be a <verbatim|Maybe Bool>, with the
  <verbatim|Nothing> value representing undefined cell values. The
  <verbatim|encode> and <verbatim|decode> functions transform a value of a
  Simplicity type to and from a list of <verbatim|Cell>s that represent the
  value. The <verbatim|executeUsing> combinator captures a common pattern of
  running a Simplicity program through an implementation of the Bit Machine
  by encoding program inputs and decoding the results. Since there is more
  than one way to compile and run Simplicity program on the Bit Machine (for
  example, see naive translation versus TCO translation), this abstraction is
  used is multiple places.

  The <verbatim|MachineCode> type alias captures canonical forms of programs
  for the Bit Machine, which is the explicit fixed point of the
  <verbatim|MachineCodeF> functor. Usually programs are built in continuation
  passing style (analogous to using difference lists to build lists), making
  use of the <verbatim|MachineCodeK> type alias. There are smart-constructors
  for each machine code that make single instruction <verbatim|MachineCodeK>
  programs. Programs are composed sequentually using ordinary function
  compostion, <verbatim|(.)>. Determinic choice between two programs is
  provided by the <verbatim|(\|\|\|)> operator. The <verbatim|nop> program is
  an alias for the identity function.

  The <verbatim|Simplicity/BitMachine/Authentic.hs> file is an implementation
  of the Bit Machine that follows the formal definition of the Bit Machine
  and fully tracks undefined values. The <verbatim|Frame> type is used for
  both read frames and write frames. The <verbatim|Active> type is captures
  the pair of active read and write frames, and the <verbatim|State> type
  captures the entire state of the Bit Machine. Lenses are used to access the
  components of the State.

  The <verbatim|runMachine> function interprets <verbatim|MachineCode> in
  accorance with the semantics of the Bit Machine, and transforms an initial
  state into a final state (possibly crashing during execution). It is meant
  to be used, in conjunction with a Simplicity translator, with
  <verbatim|executeUsing>. The <verbatim|instrumentMachine> function is a
  variant of <verbatim|runMachine> that logs statistics about memory usage
  during the execution. It is used as part of the testing for static
  analysis.

  <subsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Simplicity/BitMachine/Translate.hs> file defines the naive
  translation from Simplicity to the Bit Machine. The <verbatim|Translation>
  type wraps the <verbatim|MachineCodeK> type with phantom type parameters in
  order to make an instance suitable for a Simplicity Algebra. The
  <verbatim|translate> function translates Simplicity terms to Machine Code
  via the <verbatim|Translation> Algebra (recall that a Simplicity term in
  tagless final form is a polymorphic value that can become any Simplicity
  Algebra). The <verbatim|Simplicity/BitMachine/Translate/TCO.hs> file
  provides a similar <verbatim|Translation> Simplicity Algebra and
  <verbatim|translate> functions, but this translating using tail composition
  optimization.

  The <verbatim|Simplicity/BitMachine/Tests.hs> runs a few of the example
  Simplicity expressions through the Bit Machine implementation to test that
  the value computed by the Bit Machine matches that direct interpretation of
  the same Simplicity expressions. In this file you can see an example of how
  <verbatim|executeUsing (runMachine . translate) program> is used.

  <subsection|Static Analysis>

  The <verbatim|Simplicity/BitMachine/StaticAnalysis.hs> file performs the
  static analysis for bounding the maximum number of cells used by the Bit
  Machine when executing the naive translation of Simplicity expressions. The
  <verbatim|ExtraCellsBnd> type wraps the data needed for the static analysis
  with phantom type parameters in order ot make an instance suitable for a
  Simplicity Algebra. The <verbatim|cellsBnd> function computes the bound on
  cell use from Simplicity terms via the <verbatim|ExtraCellsBnd> Algebra.
  The <verbatim|Simplicity/BitMachine/StaticAnalysis/TCO.hs> file provides a
  similar static analysis that bounds the maximum number of cells used by the
  Bit Machine when executing the TCO translation of Simplicity expressions.

  The <verbatim|Simplicity/BitMachine/StaticAnalysis/Tests.hs> runs a few of
  the example Simplicity expressions through the static analysis and compares
  the result with the maximum cell count of executing the Bit Machine on
  various inputs. In this file you can see an example of how
  <verbatim|executeUsing (instrumentMachine . translate) program> is used.

  <chapter|C Library Guide>

  <appendix|Preliminaries>

  In this document we endeavour to be precise about the semantics surronding
  the definition of the Simplicity language. To this end we use formal
  language composed from a mix of mathematics, category theory, simple type
  theory, and functional programming. While most all our notation is standard
  in some community, we do not necessarily expect all readers to be familiar
  with ever bit of it. To that end, and to ensure completeness of our
  semantics, we give detailed definitions below of the common notation used
  throughout this document.

  Our formal langauge is phrased in terms of simple type theory, and even so,
  readers familiar with mathematics should not have too much trouble
  following it since mathematics notation already borrows heavily from simple
  type theory and everything can be interpreted in standard mathematics.

  To being with we will assume that we have a notation of a type of natural
  numbers, <math|\<bbb-N\>>, with <math|0\<of\>\<bbb-N\>>,
  <math|1:\<bbb-N\>>, and so forth for all other numbers. Given natural
  numbers <math|n:\<bbb-N\>> and <math|m:\<bbb-N\>>, we take it for granted
  that we have

  <\itemize>
    <item>notions of arithmetic including <math|n+m>, <math|n*m>, and
    <math|n<rsup|m>>;

    <item>comparison operations including <math|n\<less\>m>,
    <math|n\<leqslant\>m>, <math|n\<geqslant\>m>, and <math|n\<gtr\>m>;

    <item>when <math|n\<geqslant\>m> then the difference <math|n-m> is a
    natural number.
  </itemize>

  We will partake in several notational conviences. For example we will
  generally elide parentheses when the value they surround already has has
  its own brackes. For example,

  <\itemize>
    <item>we will write <math|f<around*|\<langle\>|x,y|\<rangle\>>> intead of
    <math|f<around*|(|<around*|\<langle\>|x,y|\<rangle\>>|)>>;

    <item>we will write <math|f<math-tt|[cafe]>> instead of
    <math|f<around*|(|<math-tt|[cafe]>|)>>;

    <item>we will write <math|l<around*|\<lceil\>|n|\<rceil\>>> instead of
    <math|l<around*|[|<around*|\<lceil\>|n|\<rceil\>>|]>>.
  </itemize>

  As you will see, we have a lot of notation with type annotations that are
  used to fully disambiguate them. Usually these type annotations can be
  completely inferred from the surrounding context and accordingly we will
  usually omit these annotations to reduce notational clutter.

  <section|Algebraic Types>

  We write the primitive unit type as <math|<value|1>>. The unique value of
  the unit type is <math|<around*|\<langle\>||\<rangle\>>\<of\><value|1>>.

  <assign|0|<math|<with|font|Bbb*|0>>>We write the primitive void type as
  <value|0>. Assuming <math|z:<value|0>> were a value of the void type, then
  <math|!<rsup|A>z\<of\>A> is a value of any type.

  Given types <math|A> and <math|B>, then <math|A+B>, <math|A\<times\>B>, and
  <math|A\<rightarrow\>B> are the sum type (also known as disjoin union
  type), (Cartesian) product type, and function type respectively. Given
  <math|a:A> and <math|b:B> we denote values of the sum and product types as

  <\eqnarray*>
    <tformat|<table|<row|<cell|<injl-long|A|B|<around*|(|a|)>>>|<cell|:>|A+
    B>|<row|<cell|<injr-long|A|B|<around*|(|b|)>>>|<cell|:>|<cell|A+
    B>>|<row|<cell|<around*|\<langle\>|a,b|\<rangle\>><rsub|A,B>>|<cell|:>|<cell|A\<times\>B>>>>
  </eqnarray*>

  To access components of sum and product types we use pattern matching. For
  example, we can define the first and second projection functions as:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<pi\><rsup|A,B><rsub|1><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|a>>|<row|<cell|\<pi\><rsup|A,B><rsub|2><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|b>>>>
  </eqnarray*>

  We write an expression of type <math|A\<rightarrow\>B> using lambda
  notation:

  <\equation*>
    \<lambda\>x:A\<point\>e\<of\>A\<rightarrow\>B
  </equation*>

  where <math|e> is an expression with <math|x\<of\>A> as a free variable
  (that may or zero or more times in <math|e>). Given
  <math|f\<of\>A\<rightarrow\>B> and <math|a:A>, then ordinary function
  application retrieves a value of type <math|B>:

  <\equation*>
    f<around*|(|a|)>\<of\>B
  </equation*>

  Per usual, the type operator <math|\<rightarrow\>> is right assocative:

  <\equation*>
    A\<rightarrow\>B\<rightarrow\>C=A\<rightarrow\><around*|(|B\<rightarrow\>C|)>
  </equation*>

  \;

  We define the identity function <math|id<rsub|A>\<of\>A\<rightarrow\>A> as

  <\equation*>
    id<rsub|A><around*|(|a|)>\<assign\>a
  </equation*>

  and given <math|f\<of\>A\<rightarrow\>B> and <math|g\<of\>B\<rightarrow\>C>
  we define their composition as

  <\equation*>
    <around*|(|g\<circ\>f|)><around*|(|a|)>\<assign\>g<around*|(|f<around*|(|a|)>|)>
  </equation*>

  \;

  When we take a product type with itself, we form a square and denote with
  exponential notation accordingly

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|2>>|<cell|\<assign\>>|<cell|A\<times\>A>>>>
  </eqnarray*>

  We can take repreated square, and we denote this by exponential notation
  with successively larger powers of two:

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|1>>|<cell|\<assign\>>|<cell|A>>|<row|<cell|A<rsup|2>>|<cell|\<assign\>>|<cell|A<rsup|1>\<times\>A<rsup|1>>>|<row|<cell|A<rsup|4>>|<cell|\<assign\>>|<cell|A<rsup|2>\<times\>A<rsup|2>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|A<rsup|2<rsup|1+n>>>|<cell|\<assign\>>|<cell|A<rsup|2<rsup|n>>
    \<times\>A<rsup|2<rsup|n>>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>>>
  </eqnarray*>

  We define the diagonal function returning a square type,
  <math|\<Delta\><rsub|A>\<of\>A\<rightarrow\>A<rsup|2>>.

  <\equation*>
    \<Delta\><rsub|A><around*|(|a|)>\<assign\><around*|\<langle\>|a,a|\<rangle\>>
  </equation*>

  <subsection|Records>

  Record types are essentially the same as product type, but with fancy
  syntax. We write a record type encloded in curly braces.

  <\equation*>
    <around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<of\>A<rsub|1>>>|<row|<cell|field<rsub|2>\<of\>A<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<of\>A<rsub|n>>>>>>|}>
  </equation*>

  If <math|R> the above record type and <math|r\<of\>R>, then we denote
  access the compontent of the record as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|r<around*|[|field<rsub|1>|]>\<of\>A<rsub|1>>|<cell|>>|<row|<cell|>|<cell|r<around*|[|field<rsub|2>|]>\<of\>A<rsub|2>>|<cell|>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|>|<cell|r<around*|[|field<rsub|n>|]>\<of\>A<rsub|n>>|<cell|>>>>
  </eqnarray*>

  To construct a record value given values
  <math|a<rsub|1>\<of\>A<rsub|1>,\<ldots\>,a<rsub|n>\<of\>A<rsub|n>>, we
  again use a curly brace notation.

  <\equation*>
    <around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<assign\>a<rsub|1>>>|<row|<cell|field<rsub|2>\<assign\>a<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<assign\>a<rsub|n>>>>>>|}>:<around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<of\>A<rsub|1>>>|<row|<cell|field<rsub|2>\<of\>A<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<of\>A<rsub|n>>>>>>|}>
  </equation*>

  <section|Functors>

  A is a functor <math|\<cal-F\>> is a type parameterized by a free type
  variable, such that whenever <math|A> is a type then
  <math|\<cal-F\><around*|(|A|)>> is a type. Given a funciton
  <math|f\<of\>A\<rightarrow\>B>, is it sometimes possible to define a new
  function <math|\<cal-F\>f\<of\>\<cal-F\>A\<rightarrow\>\<cal-F\>B> such
  that forall <math|f\<of\>A\<rightarrow\>B> and
  <math|g\<of\>B\<rightarrow\>C> we have

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-F\>id<rsub|A>>|<cell|=>|<cell|id<rsub|\<cal-F\>A>>>|<row|<cell|\<cal-F\><around*|(|f\<circ\>g|)>>|<cell|=>|<cell|\<cal-F\>f\<circ\>\<cal-F\>g>>>>
  </eqnarray*>

  When this happens we call such a functor a <dfn|covariant functor>. In this
  document, all our functors will be covariant functors, and we will simply
  call them <dfn|functor>s.

  <subsection|Option Functor>

  By way of a useful example we define <maybe> to be the option functor, also
  known as the maybe functor, as follows

  <\eqnarray*>
    <tformat|<table|<row|<cell|<maybe>A>|<cell|\<assign\>>|<cell|<value|1>+A>>|<row|<cell|<maybe>f<around*|(|<injl-long|<value|1>|A|<around*|\<langle\>||\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|A|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|<maybe>f<around*|(|<injr-long|<value|1>|A|<around*|(|a|)>>|)>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|A|<around*|(|f<around*|(|a|)>|)>>>>>>
  </eqnarray*>

  Given <math|a\<of\>A>, we define special notation for values of
  ``optional'' types <math|<maybe>A>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<emptyset\><rsub|A><rsup|<maybe>>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|A|<around*|\<langle\>||\<rangle\>>>\<of\><maybe>A>>|<row|<cell|\<eta\><rsup|S><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|A|<around*|(|a|)>>\<of\><maybe>A>>>>
  </eqnarray*>

  This notation is design to coincide with the monadic notation defined in
  Section<nbsp><reference|ss:MonadZero>.

  <subsection|List Functors>

  Given a type <math|A> we recursively define the list functor
  <math|A<rsup|\<ast\>>> and the non-empty list functor <math|A<rsup|+>>.

  \;

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|\<ast\>>>|<cell|\<assign\>>|<cell|<maybe>A<rsup|+>>>|<row|<cell|A<rsup|+>>|<cell|\<assign\>>|<cell|A\<times\>A<rsup|\<ast\>>>>|<row|<cell|f<rsup|\<ast\>><around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|B<rsup|+>>>>|<row|<cell|f<rsup|\<ast\>><around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|B<rsup|+>><around*|(|f<rsup|+><around*|(|l|)>|)>>>|<row|<cell|f<rsup|+><around*|\<langle\>|a,l|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|f<around*|(|a|)>,f<rsup|\<ast\>><around*|(|l|)>|\<rangle\>>>>>>
  </eqnarray*>

  where <math|f\<of\>A\<rightarrow\>B>.

  We will leave implicit the fact that these are inductive types and
  recursive definition over them need to be well-founded. Suffice to say that
  the definitions in this section are, in fact, all well-defined and well
  understood.

  Given a list <math|l\<of\>A<rsup|\<ast\>>> or a non-empty list
  <math|l\<of\>A<rsup|+>>, we define <math|<around*|\||l|\|>\<of\>\<bbb-N\>>
  to be its length.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\||\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|\|>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\||\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|\|>>|<cell|\<assign\>>|<cell|<around*|\||l|\|>>>|<row|<cell|<around*|\||<around*|\<langle\>|a,l|\<rangle\>>|\|>>|<cell|\<assign\>>|<cell|1+<around*|\||l|\|>>>>>
  </eqnarray*>

  \;

  To retrive an element we define lookup functions for lists and non-empty
  lists. Given a natural number <math|n\<of\>\<bbb-N\>> and either list
  <math|l\<of\>A<rsup|\<ast\>>> or a non-empty list <math|l\<of\>A<rsup|+>>,
  in both cases we define <math|l<around*|[|n|]>\<of\><maybe>A> to lookup the
  <math|n>th value in <math|l>.\ 

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)><around*|[|n|]>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|A>>>|<row|<cell|<around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)><around*|[|n|]>>|<cell|\<assign\>>|<cell|l<around*|[|n|]>>>|<row|<cell|<around*|\<langle\>|a,l|\<rangle\>><around*|[|0|]>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>>|<row|<cell|<around*|\<langle\>|a,l|\<rangle\>><around*|[|1+n|]>>|<cell|\<assign\>>|<cell|l<around*|[|n|]>>>>>
  </eqnarray*>

  Naturally the lookup will return <math|\<emptyset\>> when the lookup goes
  beyond the end of the list.

  <\lemma>
    For all <math|n\<of\>\<bbb-N\>> and <math|l\<of\>A<rsup|*\<ast\>>> or
    <math|l\<of\>A<rsup|+>>, <math|l<around*|[|n|]>=\<emptyset\>> if and only
    if <math|<around*|\||l|\|>\<leqslant\>n>.
  </lemma>

  The fold operation on a list is a most general way of consuming a list.
  Given a type <math|A> with a monoid \<odot\>, <math|e> over that type, we
  define <math|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>
  for both lists <math|l\<of\>A<rsup|\<ast\>>> and non-empty lists
  <math|l\<of\>A<rsup|+>>.

  \;

  <\eqnarray*>
    <tformat|<table|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)>>|<cell|\<assign\>>|<cell|e>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)>>|<cell|\<assign\>>|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|\<langle\>|a,l|\<rangle\>>>|<cell|\<assign\>>|<cell|a\<odot\>fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>>>>
  </eqnarray*>

  Often we will write <math|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>
  as simply <math|fold<rsup|\<odot\>><around*|(|l|)>> since usually both the
  type and the unit for a monoid is can be inferred from just its binary
  operation.

  For lists, we provide special notations for its two effective constructors
  called <dfn|nil>, <math|\<epsilon\><rsub|A>\<of\>A<rsup|\<ast\>>>, and
  <dfn|cons>, <math|a\<blacktriangleleft\>l\<of\>A<rsup|\<ast\>>> where
  <math|a\<of\>A> and <math|l\<of\>A<rsup|\<ast\>>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<epsilon\><rsub|A>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>>>|<row|<cell|a\<blacktriangleleft\>l>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|\<langle\>|a,l|\<rangle\>>>>>>
  </eqnarray*>

  As a consequence the following equations hold.

  <\eqnarray*>
    <tformat|<table|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<epsilon\><rsub|A>|)>>|<cell|=>|<cell|e>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|a<rsub|0>\<blacktriangleleft\>a<rsub|1>\<blacktriangleleft\>\<ldots\>\<blacktriangleleft\>a<rsub|n>\<blacktriangleleft\>\<epsilon\><rsub|A>|)>>|<cell|=>|<cell|a<rsub|0>\<odot\>a<rsub|1>\<odot\>\<ldots\>\<odot\>a<rsub|n>>>>>
  </eqnarray*>

  For example, given two lists <math|l<rsub|1>,l<rsub|2>\<of\>A<rsup|\<ast\>>>,
  we define the append operation <math|l<rsub|1>\<cdummy\>l<rsub|2>:A<rsup|\<ast\>>>
  using nil and cons.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<epsilon\>\<cdummy\>l>|<cell|\<assign\>>|<cell|l>>|<row|<around*|(|a\<blacktriangleleft\>l<rsub|1>|)>\<cdummy\>l<rsub|2>|<cell|\<assign\>>|<cell|a\<blacktriangleleft\><around*|(|l<rsub|1>\<cdummy\>l<rsub|2>|)>>>>>
  </eqnarray*>

  The append operation together with nil,
  <math|<around*|\<langle\>|\<cdummy\>,\<epsilon\>|\<rangle\>>>, forms a
  monoid over <math|A<rsup|*\<ast\>>>. This allows us to define the
  concatenation function <math|\<mu\><rsup|\<ast\>><rsub|A>\<of\>A<rsup|\<ast\>\<ast\>>\<rightarrow\>A<rsup|\<ast\>>>

  <\equation*>
    \<mu\><rsup|\<ast\>><rsub|A><around*|(|l|)>\<assign\>fold<rsub|A<rsup|\<ast\>>><rsup|<around*|\<langle\>|\<cdummy\>,\<epsilon\>|\<rangle\>>><around*|(|l|)>
  </equation*>

  Now it is only natural to define a function that generates a list with one
  element, <math|\<eta\><rsup|\<ast\>><rsub|A>:A\<rightarrow\>A<rsup|\<ast\>>>.

  <\equation*>
    \<eta\><rsup|\<ast\>><rsub|A><around*|(|a|)>\<assign\>a\<blacktriangleleft\>\<epsilon\>
  </equation*>
</body>

<\initial>
  <\collection>
    <associate|page-medium|papyrus>
    <associate|page-type|letter>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|LC218|<tuple|6.2.2|?>>
    <associate|LC219|<tuple|<with|mode|<quote|math>|\<bullet\>>|?>>
    <associate|LC267|<tuple|6.1|?>>
    <associate|LC313|<tuple|6.5|?>>
    <associate|LC42|<tuple|6.5|?>>
    <associate|LC98|<tuple|6.2.2|?>>
    <associate|SS:Coq:MerkleRoots|<tuple|6.5|?>>
    <associate|Serialization|<tuple|2.8|?>>
    <associate|auto-1|<tuple|1|7>>
    <associate|auto-10|<tuple|2.2.1|10>>
    <associate|auto-100|<tuple|6.5|51>>
    <associate|auto-101|<tuple|6.6|51>>
    <associate|auto-102|<tuple|6.6.1|51>>
    <associate|auto-103|<tuple|6.6.1.1|51>>
    <associate|auto-104|<tuple|6.6.2|51>>
    <associate|auto-105|<tuple|6.6.3|52>>
    <associate|auto-106|<tuple|7|52>>
    <associate|auto-107|<tuple|7.1|52>>
    <associate|auto-108|<tuple|7.2|52>>
    <associate|auto-109|<tuple|7.3|53>>
    <associate|auto-11|<tuple|2.2.2|10>>
    <associate|auto-110|<tuple|7.3.1|53>>
    <associate|auto-111|<tuple|7.3.2|55>>
    <associate|auto-112|<tuple|7.3.2.1|57>>
    <associate|auto-113|<tuple|7.3.2.2|57>>
    <associate|auto-114|<tuple|7.3.3|58>>
    <associate|auto-115|<tuple|7.3.4|59>>
    <associate|auto-116|<tuple|7.4|59>>
    <associate|auto-117|<tuple|7.4.1|59>>
    <associate|auto-118|<tuple|7.5|?>>
    <associate|auto-119|<tuple|7.6|?>>
    <associate|auto-12|<tuple|2.2.3|10>>
    <associate|auto-120|<tuple|7.7|?>>
    <associate|auto-121|<tuple|7.7.1|?>>
    <associate|auto-122|<tuple|7.7.2|?>>
    <associate|auto-123|<tuple|8|?>>
    <associate|auto-124|<tuple|A|?>>
    <associate|auto-125|<tuple|A.1|?>>
    <associate|auto-126|<tuple|A.1.1|?>>
    <associate|auto-127|<tuple|A.2|?>>
    <associate|auto-128|<tuple|A.2.1|?>>
    <associate|auto-129|<tuple|A.2.2|?>>
    <associate|auto-13|<tuple|2.2.4|10>>
    <associate|auto-14|<tuple|2.2.5|11>>
    <associate|auto-15|<tuple|2.2.6|11>>
    <associate|auto-16|<tuple|2.2.7|11>>
    <associate|auto-17|<tuple|2.2.8|11>>
    <associate|auto-18|<tuple|2.2.9|11>>
    <associate|auto-19|<tuple|2.2.10|11>>
    <associate|auto-2|<tuple|1.1|7>>
    <associate|auto-20|<tuple|2.2.11|12>>
    <associate|auto-21|<tuple|2.3|12>>
    <associate|auto-22|<tuple|2.3.1|12>>
    <associate|auto-23|<tuple|2.3.2|13>>
    <associate|auto-24|<tuple|2.3.3|17>>
    <associate|auto-25|<tuple|2.3.4|17>>
    <associate|auto-26|<tuple|2.3.5|18>>
    <associate|auto-27|<tuple|2.3.6|18>>
    <associate|auto-28|<tuple|2.4|18>>
    <associate|auto-29|<tuple|2.5|18>>
    <associate|auto-3|<tuple|2|9>>
    <associate|auto-30|<tuple|2.5.1|19>>
    <associate|auto-31|<tuple|2.5.2|19>>
    <associate|auto-32|<tuple|2.1|19>>
    <associate|auto-33|<tuple|2.5.2.1|20>>
    <associate|auto-34|<tuple|2.5.2.2|20>>
    <associate|auto-35|<tuple|2.5.2.3|20>>
    <associate|auto-36|<tuple|2.5.2.4|21>>
    <associate|auto-37|<tuple|2.5.2.5|21>>
    <associate|auto-38|<tuple|2.5.2.6|22>>
    <associate|auto-39|<tuple|2.5.3|22>>
    <associate|auto-4|<tuple|2.1|9>>
    <associate|auto-40|<tuple|2.5.3.1|22>>
    <associate|auto-41|<tuple|2.6|24>>
    <associate|auto-42|<tuple|2.6.1|24>>
    <associate|auto-43|<tuple|2.6.1.1|24>>
    <associate|auto-44|<tuple|2.6.1.2|27>>
    <associate|auto-45|<tuple|2.6.2|27>>
    <associate|auto-46|<tuple|2.7|27>>
    <associate|auto-47|<tuple|2.8|28>>
    <associate|auto-48|<tuple|2.8.1|28>>
    <associate|auto-49|<tuple|3|29>>
    <associate|auto-5|<tuple|2.1.1|9>>
    <associate|auto-50|<tuple|3.1|29>>
    <associate|auto-51|<tuple|3.1.1|29>>
    <associate|auto-52|<tuple|3.1.2|29>>
    <associate|auto-53|<tuple|3.1.3|30>>
    <associate|auto-54|<tuple|3.1.3.1|31>>
    <associate|auto-55|<tuple|3.2|31>>
    <associate|auto-56|<tuple|3.2.1|31>>
    <associate|auto-57|<tuple|3.2.2|31>>
    <associate|auto-58|<tuple|3.2.3|31>>
    <associate|auto-59|<tuple|3.2.4|31>>
    <associate|auto-6|<tuple|2.1.1.1|9>>
    <associate|auto-60|<tuple|3.3|32>>
    <associate|auto-61|<tuple|3.3.1|32>>
    <associate|auto-62|<tuple|3.3.2|33>>
    <associate|auto-63|<tuple|3.3.2.1|33>>
    <associate|auto-64|<tuple|3.3.3|34>>
    <associate|auto-65|<tuple|3.3.3.1|34>>
    <associate|auto-66|<tuple|3.3.3.2|35>>
    <associate|auto-67|<tuple|3.4|35>>
    <associate|auto-68|<tuple|3.4.1|37>>
    <associate|auto-69|<tuple|3.4.1.1|38>>
    <associate|auto-7|<tuple|2.1.2|9>>
    <associate|auto-70|<tuple|3.4.1.2|38>>
    <associate|auto-71|<tuple|3.4.1.3|38>>
    <associate|auto-72|<tuple|3.5|38>>
    <associate|auto-73|<tuple|3.5.1|39>>
    <associate|auto-74|<tuple|4|39>>
    <associate|auto-75|<tuple|4.1|41>>
    <associate|auto-76|<tuple|5|42>>
    <associate|auto-77|<tuple|5.1|43>>
    <associate|auto-78|<tuple|6|43>>
    <associate|auto-79|<tuple|6.1|43>>
    <associate|auto-8|<tuple|2.1.2.1|10>>
    <associate|auto-80|<tuple|6.2|43>>
    <associate|auto-81|<tuple|6.2.1|43>>
    <associate|auto-82|<tuple|6.2.2|44>>
    <associate|auto-83|<tuple|6.2.2.1|44>>
    <associate|auto-84|<tuple|6.2.2.2|45>>
    <associate|auto-85|<tuple|6.2.2.3|45>>
    <associate|auto-86|<tuple|6.2.3|45>>
    <associate|auto-87|<tuple|6.3|45>>
    <associate|auto-88|<tuple|6.3.1|45>>
    <associate|auto-89|<tuple|6.3.2|46>>
    <associate|auto-9|<tuple|2.2|10>>
    <associate|auto-90|<tuple|6.3.3|47>>
    <associate|auto-91|<tuple|6.4|47>>
    <associate|auto-92|<tuple|6.1|48>>
    <associate|auto-93|<tuple|6.4.1|48>>
    <associate|auto-94|<tuple|6.4.2|49>>
    <associate|auto-95|<tuple|6.4.3|49>>
    <associate|auto-96|<tuple|6.4.4|50>>
    <associate|auto-97|<tuple|6.4.4.1|51>>
    <associate|auto-98|<tuple|6.4.5|51>>
    <associate|auto-99|<tuple|6.4.6|51>>
    <associate|docs-internal-guid-af5ffdcd-7114-eda6-c80e-f3a224e6380a|<tuple|3.2.1|?>>
    <associate|fig:inheritance|<tuple|6.1|?>>
    <associate|footnote-1|<tuple|1|?>>
    <associate|footnote-2.1|<tuple|2.1|20>>
    <associate|footnote-3.1|<tuple|3.1|?>>
    <associate|footnr-2.1|<tuple|2.1|20>>
    <associate|footnr-3.1|<tuple|3.1|?>>
    <associate|full-adder-LHS|<tuple|2.3|16>>
    <associate|full-adder-RHS|<tuple|2.2|16>>
    <associate|full-adder-spec|<tuple|2.1|15>>
    <associate|ss:AssertMerkleRoot|<tuple|3.3.3|33>>
    <associate|ss:BTDenotationalSemantics|<tuple|3.4.1.1|?>>
    <associate|ss:BTMerkleRoots|<tuple|3.4.1.2|?>>
    <associate|ss:BitcoinTransactions|<tuple|3.4.1|?>>
    <associate|ss:DenotationalSemanticsOfFullSimplicity|<tuple|7.6|52>>
    <associate|ss:MonadZero|<tuple|3.3.1|32>>
    <associate|ss:RepresentingValuesAsCellArrays|<tuple|2.5.1|19>>
    <associate|ss:Serialization|<tuple|2.8|28>>
    <associate|ss:pruning|<tuple|3.3.3.1|34>>
    <associate|ss:salted|<tuple|3.3.3.2|34>>
    <associate|thm:CSCT|<tuple|2.2|18>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|figure>
      <tuple|normal|Example state of the Bit Machine.|<pageref|auto-32>>

      <tuple|normal|The inheritance hierarchy of algebras for Simplicity's
      languge extensions in Coq.|<pageref|auto-92>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      1.1<space|2spc>Design Goals <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Core
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      2.1<space|2spc>Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>

      <with|par-left|<quote|1tab>|2.1.1<space|2spc>Abstract Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|2tab>|2.1.1.1<space|2spc>Formal Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1tab>|2.1.2<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|2tab>|2.1.2.1<space|2spc>Formal Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      2.2<space|2spc>Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>

      <with|par-left|<quote|1tab>|2.2.1<space|2spc>Identity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1tab>|2.2.2<space|2spc>Composition
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1tab>|2.2.3<space|2spc>Constant Unit
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1tab>|2.2.4<space|2spc>Left Injection
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1tab>|2.2.5<space|2spc>Right Injection
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1tab>|2.2.6<space|2spc>Case
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1tab>|2.2.7<space|2spc>Pair
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|1tab>|2.2.8<space|2spc>Take
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|1tab>|2.2.9<space|2spc>Drop
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|1tab>|2.2.10<space|2spc>Formal Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1tab>|2.2.11<space|2spc>Formal Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      2.3<space|2spc>Example Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>

      <with|par-left|<quote|1tab>|2.3.1<space|2spc>Bit Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <with|par-left|<quote|1tab>|2.3.2<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>>

      <with|par-left|<quote|1tab>|2.3.3<space|2spc>Bitwise Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1tab>|2.3.4<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      <with|par-left|<quote|1tab>|2.3.5<space|2spc>Modular Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      <with|par-left|<quote|1tab>|2.3.6<space|2spc>Elliptic Curve Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27>>

      2.4<space|2spc>Completeness Theorem
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28>

      2.5<space|2spc>Operational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>

      <with|par-left|<quote|1tab>|2.5.1<space|2spc>Repesenting Values as Cell
      Arrays <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|2.5.2<space|2spc>Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <with|par-left|<quote|2tab>|2.5.2.1<space|2spc>Frame Instructions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|2tab>|2.5.2.2<space|2spc>Active Write Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|2tab>|2.5.2.3<space|2spc>Active Read Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <with|par-left|<quote|2tab>|2.5.2.4<space|2spc>Abort Instruction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36>>

      <with|par-left|<quote|2tab>|2.5.2.5<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>>

      <with|par-left|<quote|2tab>|2.5.2.6<space|2spc>Crashing the Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38>>

      <with|par-left|<quote|1tab>|2.5.3<space|2spc>Executing Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>>

      <with|par-left|<quote|2tab>|2.5.3.1<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>>

      2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>

      <with|par-left|<quote|1tab>|2.6.1<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>>

      <with|par-left|<quote|2tab>|2.6.1.1<space|2spc>Maximum Cell Count Bound
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>>

      <with|par-left|<quote|2tab>|2.6.1.2<space|2spc>Maximum Frame Count
      Bound <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>>

      <with|par-left|<quote|1tab>|2.6.2<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45>>

      2.7<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>

      2.8<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>

      <with|par-left|<quote|1tab>|2.8.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Simplicity
      Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49><vspace|0.5fn>

      3.1<space|2spc>Monadic Effects <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>

      <with|par-left|<quote|1tab>|3.1.1<space|2spc>Kleisli Morphisms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>>

      <with|par-left|<quote|1tab>|3.1.2<space|2spc>Cartesian Strength
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52>>

      <with|par-left|<quote|1tab>|3.1.3<space|2spc>Monadic Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53>>

      <with|par-left|<quote|2tab>|3.1.3.1<space|2spc>Identity Monad
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54>>

      3.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55>

      <with|par-left|<quote|1tab>|3.2.1<space|2spc>Elided Computation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56>>

      <with|par-left|<quote|1tab>|3.2.2<space|2spc>Witness Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57>>

      <with|par-left|<quote|1tab>|3.2.3<space|2spc>Serialization with
      Witnesses <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58>>

      <with|par-left|<quote|1tab>|3.2.4<space|2spc>Type Inference with
      Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-59>>

      3.3<space|2spc>Assertions and Failure
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-60>

      <with|par-left|<quote|1tab>|3.3.1<space|2spc>Monad Zero
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-61>>

      <with|par-left|<quote|1tab>|3.3.2<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-62>>

      <with|par-left|<quote|2tab>|3.3.2.1<space|2spc>Option Monad
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-63>>

      <with|par-left|<quote|1tab>|3.3.3<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-64>>

      <with|par-left|<quote|2tab>|3.3.3.1<space|2spc>Pruning Unused
      <with|font-family|<quote|ss>|case> Branches
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-65>>

      <with|par-left|<quote|2tab>|3.3.3.2<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-66>>

      3.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-67>

      <with|par-left|<quote|1tab>|3.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-68>>

      <with|par-left|<quote|2tab>|3.4.1.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-69>>

      <with|par-left|<quote|2tab>|3.4.1.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-70>>

      <with|par-left|<quote|2tab>|3.4.1.3<space|2spc>Schnorr Signature
      Aggregation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-71>>

      3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-72>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-73>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Jets>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-74><vspace|0.5fn>

      4.1<space|2spc>Example: The Standard Single Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-75>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Delegation>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-76><vspace|0.5fn>

      5.1<space|2spc>Unbounded Loops <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-77>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-78><vspace|0.5fn>

      6.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-79>

      6.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-80>

      <with|par-left|<quote|1tab>|6.2.1<space|2spc>The ``Initial''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-81>>

      <with|par-left|<quote|1tab>|6.2.2<space|2spc>The ``Final''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-82>>

      <with|par-left|<quote|2tab>|6.2.2.1<space|2spc>Simplicity Algebras
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-83>>

      <with|par-left|<quote|2tab>|6.2.2.2<space|2spc>The ``Final''
      Representation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-84>>

      <with|par-left|<quote|2tab>|6.2.2.3<space|2spc>Constructing ``Final''
      Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-85>>

      <with|par-left|<quote|1tab>|6.2.3<space|2spc>Why two representations of
      Terms? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-86>>

      6.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-87>

      <with|par-left|<quote|1tab>|6.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-88>>

      <with|par-left|<quote|1tab>|6.3.2<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-89>>

      <with|par-left|<quote|1tab>|6.3.3<space|2spc>SHA256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-90>>

      6.4<space|2spc>The Hierarchy of Simplicity Language Extensions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-91>

      <with|par-left|<quote|1tab>|6.4.1<space|2spc>Witness
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-93>>

      <with|par-left|<quote|1tab>|6.4.2<space|2spc>Assertion
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-94>>

      <with|par-left|<quote|1tab>|6.4.3<space|2spc>Delegation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-95>>

      <with|par-left|<quote|1tab>|6.4.4<space|2spc>Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-96>>

      <with|par-left|<quote|1tab>|6.4.5<space|2spc>Jets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-97>>

      <with|par-left|<quote|1tab>|6.4.6<space|2spc>Full Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-98>>

      6.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-99>

      6.6<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-100>

      <with|par-left|<quote|1tab>|6.6.1<space|2spc>Bit Machine Code
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-101>>

      <with|par-left|<quote|2tab>|6.6.1.1<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-102>>

      <with|par-left|<quote|1tab>|6.6.2<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-103>>

      <with|par-left|<quote|1tab>|6.6.3<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-104>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-105><vspace|0.5fn>

      7.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-106>

      7.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-107>

      7.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-108>

      <with|par-left|<quote|1tab>|7.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-109>>

      <with|par-left|<quote|1tab>|7.3.2<space|2spc>Multi-bit Words
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-110>>

      <with|par-left|<quote|2tab>|7.3.2.1<space|2spc>Arithmetic operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-111>>

      <with|par-left|<quote|2tab>|7.3.2.2<space|2spc>Bit-wise operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-112>>

      <with|par-left|<quote|1tab>|7.3.3<space|2spc>Generic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-113>>

      <with|par-left|<quote|1tab>|7.3.4<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-114>>

      7.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-115>

      <with|par-left|<quote|1tab>|7.4.1<space|2spc>Bitcoin Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-116>>

      7.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-117>

      7.6<space|2spc>Denotational Semantics of Full Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-118>

      7.7<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-119>

      <with|par-left|<quote|1tab>|7.7.1<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-120>>

      <with|par-left|<quote|1tab>|7.7.2<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-121>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-122><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      A<space|2spc>Preliminaries> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-123><vspace|0.5fn>

      A.1<space|2spc>Algebraic Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-124>

      <with|par-left|<quote|1tab>|A.1.1<space|2spc>Records
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-125>>

      A.2<space|2spc>Functors <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-126>

      <with|par-left|<quote|1tab>|A.2.1<space|2spc>Option Functor
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-127>>

      <with|par-left|<quote|1tab>|A.2.2<space|2spc>List Functors
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-128>>
    </associate>
  </collection>
</auxiliary>
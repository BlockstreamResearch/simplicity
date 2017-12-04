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

    <with|par-left|2tab|2.5.2.1<space|2spc>Frame operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>>

    <with|par-left|2tab|2.5.2.2<space|2spc>Active Write Frame operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <with|par-left|2tab|2.5.2.3<space|2spc>Active Read Frame operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    <with|par-left|2tab|2.5.2.4<space|2spc>Crashing the Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-36>>

    <with|par-left|2tab|2.5.2.5<space|2spc>Bit Machine programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>>

    <with|par-left|1tab|2.5.3<space|2spc>Executing Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-38>>

    <with|par-left|2tab|2.5.3.1<space|2spc>Tail Composition Optimisation
    (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39>>

    2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-40>

    <with|par-left|1tab|2.6.1<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-41>>

    <with|par-left|1tab|2.6.2<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-42>>

    <with|par-left|1tab|2.6.3<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-43>>

    2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>

    <with|par-left|1tab|2.7.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-45>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Full
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46><vspace|0.5fn>

    3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>

    <with|par-left|1tab|3.1.1<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49>

    3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>

    <with|par-left|1tab|3.3.1<space|2spc>Hidden Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51>>

    <with|par-left|1tab|3.3.2<space|2spc>Serialization with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52>>

    <with|par-left|1tab|3.3.3<space|2spc>Type Inference with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53>>

    3.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54>

    <with|par-left|1tab|3.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55>>

    <with|par-left|1tab|3.4.2<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56>>

    3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57>

    <with|par-left|1tab|3.5.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Jetted
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-59><vspace|0.5fn>

    4.1<space|2spc>Example: The Standard Single Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-60>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Extended
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-61><vspace|0.5fn>

    5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-62>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-63><vspace|0.5fn>

    6.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-64>

    6.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-65>

    <with|par-left|1tab|6.2.1<space|2spc>The ``Initial'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-66>>

    <with|par-left|1tab|6.2.2<space|2spc>The ``Final'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-67>>

    <with|par-left|2tab|6.2.2.1<space|2spc>Simplicity Algebras
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-68>>

    <with|par-left|2tab|6.2.2.2<space|2spc>The ``Final'' Representation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-69>>

    <with|par-left|2tab|6.2.2.3<space|2spc>Constructing ``Final'' Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-70>>

    <with|par-left|1tab|6.2.3<space|2spc>Why two representations of Terms?
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-71>>

    6.3<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-72>

    <with|par-left|1tab|6.3.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-73>>

    <with|par-left|1tab|6.3.2<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-74>>

    6.4<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-75>

    <with|par-left|1tab|6.4.1<space|2spc>Bit Machine Code
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-76>>

    <with|par-left|2tab|6.4.1.1<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-77>>

    6.5<space|2spc>Translating Simplicity to the Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-78>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-79><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-80><vspace|0.5fn>
  </table-of-contents>

  <chapter|Introduction>

  <section|Design Goals>

  <chapter|Core Simplicity>

  Simplicty is a typed functional programming language based on Gentzen's
  sequent calculus. \ The core language consists of nine combinators for
  forming expressions. \ These nine combinators capture the computational
  power of Simplicity. In later chapters, other combinators will extend this
  core language and provide other effects to handle input and access the
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
  from <math|A> and <math|B>. \ The sum type has left-tagged values
  <math|<injl-long|A|B|<around*|(|a|)>>:A+ B> for each value <math|a : A>,
  and right-tagged values <math|<injr-long|A|B|<around*|(|b|)>>:A+ B> for
  each value <math|b : B>.

  The type <math|A\<times\>B> contains pairs of values from <math|A> and
  <math|B>. For each pair of values <math|a :A> and <math|b : B> there is
  value <math|>for the pair written as <math|><pair-long|a|b|A|B>.

  Simplicity has neither function types nor recursive types. Every type in
  Simplicity can only contain a finite number of values. \ For example, the
  type <math|<value|1>+<value|1>> has exactly two values, namely
  <injl-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>> and
  <injr-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>. The type
  <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  has exactly four values. \ As you can see, the number of values that a type
  contains can be easily calculated by interpreting the type as an arithmetic
  expression. Be aware that these types are not arithmetic expressions. \ For
  example, the types <math|<around*|(|<value|1>+<value|1>|)>+<around*|(|<value|1>+<value|1>|)>>
  and <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  are distinct and not interchangable.

  The type annotations on values can often be infered and are tedious to
  write out. \ Therefore we will usually omit the annotations, writing
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
  types. \ Every Simplicity term is associated with an input type and an
  output type and we write a type annotated term as <math|t:A\<vdash\>B>
  where <math|t> is the term, <math|A> is the input type and <math|B> is the
  output type. We write <math|<around*|\<llbracket\>|t|\<rrbracket\>>> for
  the function that the term <math|t> denotes.

  Core Simplicty has nine combinators for forming well-typed terms.

  <subsection|Identity>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<samp|iden><math|<rsub|A>
    : A\<vdash\>A>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|a|)>\<assign\>a
  </equation*>

  For every type <math|A> there we have an identity term that denotes the
  identity function for that type.\ 

  Like the type annotations on values, the type argument for <math|iden>
  usually can be infered and therefore we will usually omit (as we did for
  the denotation equation above). \ Similarly, we will usually omit the type
  arguments for all the other Simplicity combinators.

  <subsection|Composition>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : B\<vdash\>C>>>>>>>>|<row|<cell|<math|<math-ss|comp><rsub|A,B,C> s t:
    A\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|comp> s
    t|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>><around*|(|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>|)>
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
    <around*|\<llbracket\>|<math-ss|unit>|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<langle\>||\<rangle\>>
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
    <around*|\<llbracket\>|<math-ss|injl>
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
    <around*|\<llbracket\>|<math-ss|injr>
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
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|case> s
    t|\<rrbracket\>><around*|\<langle\>|<injl|<around*|(|a|)>,c>|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case>
    s t|\<rrbracket\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|\<langle\>|b,c|\<rangle\>>>>>>
  </eqnarray*>

  The case combinator is Simplicity's only branching operation. \ Given a
  pair of values with the first component being a sum type, this combinator
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
    <around*|\<llbracket\>|<math-ss|pair> s
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
    <around*|\<llbracket\>|<math-ss|take>
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
    <around*|\<llbracket\>|<math-ss|drop>
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
  Booleans, or Bit. \ We will denote this type by <math|<2>>.

  <\equation*>
    <2>\<assign\><value|1>+<value|1>
  </equation*>

  To be clear, we are not doing arithmetic above; we are instead defining the
  type for bit to be the sum type of two unit types.

  We will name the two values of this type, <math|0<rsub|<2>>> and
  <math|1<rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|0<rsub|<2>>>|<cell|\<assign\>>|<cell|<injl|<around*|\<langle\>||\<rangle\>>>:<2>>>|<row|<cell|1<rsub|<2>>>|<cell|\<assign\>>|<cell|<injr|<around*|\<langle\>||\<rangle\>>>:<2>>>>>
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
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|false>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|0<rsub|<2>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|1<rsub|<2>>>>>>
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
    t|\<rrbracket\>><around*|\<langle\>|1,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|cond>
    s t|\<rrbracket\>><around*|\<langle\>|0,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>>>>>
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
  <math|<math-ss|and-func>:<2>\<times\><2>\<vdash\><2>> \ and
  <math|<math-ss|or-func>:<2>\<times\><2>\<vdash\><2>>, then the two
  arguments to <samp|and-func> and <samp|or-func> would both need to be fully
  evaluated under strict semantics (see Section<nbsp><with|color|red|TODO>).
  For the <samp|not> combinator, this is less of an issue, but we define it
  in combinator form to be consistent.

  <subsection|Arithmetic>

  In the previous section I was relatively detailed with the annotations
  given to the definitions. \ Going forward I will be a bit more lax in the
  presentation. We will also start using some notation to abbrevate terms.

  <\eqnarray*>
    <tformat|<table|<row|<cell|s\<times\>t>|<cell|\<assign\>>|<cell|<math-ss|pair>
    s t>>|<row|<cell|s;t>|<cell|\<assign\>>|<cell|<math-ss|comp> s t>>>>
  </eqnarray*>

  with the <math|\<times\>> operator having higher precidence than the
  <math|;> operator.

  Composition of sequences of \ <samp|drop> and <samp|take> with <samp|ident>
  is a very common way of picking data out of nested tuples of input. \ To
  make this more concise we will use the following notation.

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
    \<times\><2><rsup|2>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|<2><rsup|2n>>|<cell|\<assign\>>|<cell|<2><rsup|n>
    \<times\><2><rsup|n>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>>>
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
    <tformat|<table|<row|<cell|<around*|\<lceil\>|0<rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\<lceil\>|1<rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|1>>|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2n>>|<cell|\<assign\>>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>>>>
  </eqnarray*>

  We will also make use of the following variation of this value conversion
  function.

  <\equation*>
    <around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|n,m>\<assign\><around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\>2<rsup|m>+<around*|\<lceil\>|b|\<rceil\>><rsub|m>
  </equation*>

  These value conversion functions are all injective (one-to-one).

  Using techniques familiar from digitial logic we can build an adders and
  full adders from our Boolean operations defined in the previous section.
  \ We begin with definitions of the single bit adder and full adder.

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
  <math|<math-ss|full-adder><rsub|1>>). \ We will illustrate this for a
  single case for <math|<math-ss|adder><rsub|1>> where <math|a=1<rsub|<2>>>
  and <math|b=0<rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|cond>
    <around*|(|<math-ss|iden>\<times\><math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false>\<times\><math-ss|iden>|)>|\<rrbracket\>><around*|\<langle\>|1<rsub|<2>>,0<rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|iden>\<times\><math-ss|not>
    <math-ss|iden>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|not>
    <math-ss|iden>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>; <around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|unit>|\<rrbracket\>><around*|(|0<rsub|<2>>|)>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|0<rsub|<2>>,<around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|0<rsub|<2>>,1<rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|0<rsub|2>|\<rceil\>><rsub|1>\<cdot\>2<rsup|1>+<around*|\<lceil\>|1<rsub|2>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|0\<cdot\>2+1>>|<row|<cell|>|<cell|=>|<cell|1>>|<row|<cell|>|<cell|=>|<cell|1+0>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|1<rsub|2>|\<rceil\>><rsub|1>+<around*|\<lceil\>|0<rsub|2>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>>>>>
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
    induction on <math|n>. \ As mentioned before,
    <math|<math-ss|full-adder><rsub|1>> case is easily checked by verifying
    all eight possible inputs. Next we prove that
    <math|<math-ss|full-adder><rsub|2n>> meets its specification under the
    assumption that <math|<math-ss|full-adder><rsub|n>> does. \ Specifically
    we want to show that

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
  be, in principle, expressed as a large lookup table. \ It is possible to
  encode these lookup tables as Simplicity expressions. \ The formal proof of
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
  of expressions. \ However, they are not suitable for determining the
  computation resources needed to evaluate expressions. \ For this reason we
  define an operational semantics for Simplicity via an abstract machine we
  call the <dfn|Bit Machine>.

  <subsection|Repesenting Values as Cell Arrays>

  <assign|carr|<macro|x|<verbatim|[<arg|x>]>>><assign|cearr|<macro|x|<verbatim|[<arg|x><underline|]>>>><assign|rep|<macro|x|y|<math|\<ulcorner\><arg|x>\<urcorner\><rsub|<arg|y>>>>>Values
  in the Bit Machine are represented by arrays of cells where each cell
  contains one of three values: a <verbatim|0> value, a <verbatim|1> value,
  or a <verbatim|?> value which we call an undefined value. \ We write an
  array of cell by enclosing a sequence of cells with square brackets (e.g.
  <carr|1?0>). \ We denote the length of an array using
  <math|<around*|\||\<cdummy\>|\|>>. \ For example,
  <math|<around*|\||<carr|1?0>|\|>=3>. The concatenation of two arrays,
  <math|a> and <math|b> is denoted by <math|a\<cdot\>b>, and replication of
  an array <math|n> times is denoted by expontiation, <math|a<rsup|n>>.
  \ Sometime we will omit the dot whed performing concatenation.

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
  read-frame stack and a write-frame stack. \ The top elements of the two
  stacks are called the <dfn|active read frame> and the <dfn|active write
  frame> respectively. \ The other frames are called inactive read-frames or
  inactive write-frames.

  <big-figure|<tabular|<tformat|<cwith|1|1|1|-1|cell-tborder|2px>|<cwith|5|5|1|-1|cell-bborder|2px>|<cwith|1|1|1|-1|cell-bborder|1px>|<table|<row|<cell|read
  frame stack>|<cell|write frame stack>>|<row|<cell|<carr|100<underline|1>1??110101000>>|<cell|<cearr|11??1101>>>|<row|<cell|<carr|<underline|0>000>>|<cell|<carr|111<underline|?>?>>>|<row|<cell|<cearr|>>|<cell|>>|<row|<cell|<carr|<underline|1>0>>|<cell|>>>>>|Example
  state of the Bit Machine.>

  Notationally we will write a stack of read frames as
  <math|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>>,
  with <math|r<rsub|0>> as the active read frame. We will write a stack of
  write frames in the opposite order, as <math|w<rsub|0>\<vartriangleleft\>w<rsub|1>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>>
  with <math|w<rsub|0><rsub|>> as the active write frame. In both cases we
  denote an empty stack as <math|\<varnothing\>>. We write a state of the Bit
  Machine as <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>
  where <math|\<Theta\>> is a read frame stack and <math|\<Xi\>> is a write
  frame stack and <math|r<rsub|0>> is the active read frame and
  <math|w<rsub|0>> is the active write frame.<\footnote>
    The notation for the Bit Machine's state is intended to mimic the gap
    buffer used in our C implemenation of the Bit Machine (see
    <with|color|red|TODO>).
  </footnote>

  The Bit Machine has nine basic instructions that, when executed, transform
  the Bit Machine's state. \ We denote these basic instructions as
  <math|i:S\<rightsquigarrow\>S<rprime|'>>, where <math|i> is the
  instructions's name, <math|S> is a state of the Bit Machine before
  executing the instruction, and <math|S<rprime|'>> is the state of the
  machine after the successful execution of the instructions.

  <subsubsection|Frame operations>

  Our first three basic instructions, create, move, and delete active frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|newFrame<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
    \<rightsquigarrow\><around*|[|\<Theta\>\|<emptyFrame><carr|?><rsup|n>\<vartriangleleft\>w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|moveFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0><emptyFrame>\<vartriangleleft\>w<rsub|1>\<vartriangleleft\>\<Xi\>|]>
    \<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<vartriangleright\><emptyFrame>w<rsub|0>\|w<rsub|1>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|dropFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>\|\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|\<Xi\>|]>>>>>
  </eqnarray*>

  Executing a <math|newFrame<around*|(|n|)>> instruction pushes a new frame
  of length <math|n> onto the write frame stack. This new frame has its
  cursor at the beginning of the frame and the entire frame is filled with
  undefined values. It is legal for the new frame to have length 0.

  Executing the <math|moveFrame> instruction moves the top frame of the write
  frame stack to the read frame stack. \ This instruction is only legal to
  execute when the cursor of the active write frame is at the end of the
  frame. The cursor is reset to the beginning of the frame when it is placed
  onto the read frame stack.

  Executing the <math|dropFrame> instructions removes the top frame of the
  read frame stack.

  <subsubsection|Active Write Frame operations>

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
  \ Note that undefined cell values are legal to copy. The trivial
  instruction <math|copy<around*|(|0|)>> is legal and executing it is
  effectively a nop.

  <subsubsection|Active Read Frame operations>

  The last two instructions are used to manipulate the active read frame's
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
  legal and executing them are effective nops.

  <subsubsection|Crashing the Bit Machine>

  All of the above instructions can only be executed in a state that matches
  the pattern of the input state shown. If the operation are executed in any
  other state, the Bit Machine instead crashes.

  The ninth and final basic instruction is called <math|crash>. It always
  crashes the Bit Machine when executed, regardless of what state the machine
  is in. The <math|crash> instruction has no corresponding rule because there
  is no state that it can execute successfully in.

  <subsubsection|Bit Machine programs>

  The basic instructions of the Bit Machine are combined to produce programs
  that take the Bit Machine through a sequence of states. \ We write
  <math|S\<twoheadrightarrow\>S<rprime|'>> to indicate a sequence of states
  that start from <math|S> and ends in <math|S<rprime|'>>. \ We write
  <math|k:S\<twoheadrightarrow\>S<rprime|'>> for a program, <math|k>, that,
  when executed, sucessfully transfroms an initial state <math|S> to the
  final state <math|S<rprime|'>>.

  <\equation*>
    nop:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  We write <math|nop> for the trival program with no instructions. \ The
  inital and final states are identical in this case.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>|<row|<cell|<math|i<rsub|>:
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>>>>
  </with>

  Every basic instruction is also program whose intial and final states match
  those of the basic instruction.

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|k<rsub|0>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>|<cell|<math|k<rsub|1>
    : <around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>>>|<row|<cell|<math|k<rsub|0>;k<rsub|1>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>
  </with>

  \;

  We write <math|k<rsub|0>;k<rsub|1>> for a sequence of two programs,
  <math|k<rsub|0>> and <math|k<rsub|1>>. \ The Bit Machine executes the two
  programs in turn, concatenating the sequence of states of the two programs.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|k<rsub|0>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>|<row|<cell|<math|k<rsub|0><around*|\|||\|>k<rsub|1><rsub|>:
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|k<rsub|1>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>|<row|<cell|<math|k<rsub|0><around*|\|||\|>k<rsub|1><rsub|>:
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>
  </with>

  Lastly, we define <math|k<rsub|0><around*|\|||\|>k<rsub|1>> as a
  deterministic choice between two programs, <math|k<rsub|0>> and
  <math|k<rsub|1>>. \ When executing a determinsitc choice, the value under
  the active read frame's cursor decides which one of the two programs are
  executed. \ When encountering a determinisitc choice, the active read
  frame's cursor must not be at the end of its array and the cell under the
  cursor cannot be an undefined value, otherwise the machine crashes.

  <\equation*>
    n\<star\>k\<assign\>fwd<around*|(|n|)>;k;bwd<around*|(|n|)>
  </equation*>

  The <math|n\<star\>k> notation (called ``bump'') is for a program that
  temporarily advances the active read frame's cursor when executing
  <math|k>.

  <\theorem>
    \;

    <\with|par-mode|center>
      <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|k:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>|<row|<cell|<math|n\<star\>k:
      <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>
    </with>

    \;
  </theorem>

  <subsection|Executing Simplicity>

  We recursively translate a Core Simplicity program, <math|t : A
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
      <around*|\<llangle\>|t|\<rrangle\>>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any stacks <math|><math|\<Theta\>>, <math|\<Xi\>>, and
    any natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have\ 

  <\equation*>
    <around*|\<llangle\>|t|\<rrangle\>>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
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
  a second procedure. \ Normally the first procedure's stack frame would be
  free after the second procedure returns. The tail call optimization instead
  frees the first procedure's stack frame prior to the call to the second
  procedure instead. \ This can reduce the overall memory use of the program.

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
  recursive call to <math|<TCOon|\<cdummy\>>> instead. \ The definition of
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
      <TCOoff|t>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
    </equation*>

    and

    <\equation*>
      <TCOon|t>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0><emptyFrame><rsub|><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any frame <math|r<rsub|1>>, any stacks
    <math|><math|\<Theta\>>, <math|\<Xi\>>, and any natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have\ 

  <\equation*>
    <TCOoff|t>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
  </equation*>

  <section|Static Analysis>

  <subsection|Space Resources>

  The primary source of memory resources used by the Bit Machine is the cells
  used by all the frames that make of the state of Bit Machine. \ A secondary
  source of memory resources used comes from the overhead of the frames
  themselves, which need to store their bounderies or sizes, and the position
  of their cursors. In our analysis we will make a simplifying assumption
  that these bounderies / sizes / positions values are all of constant size.
  \ This assumption holds when the Bit Machine is implemented on real
  hardware which has an upper bound on its addressable memory and there is a
  limit on the number of Cells that can be held anyways.

  To bound these resources we perform a static analysis to compute an upper
  bound on the maximum number of cells needed when executing a Simplicity
  program on the Bit Machine for any input, and we compute an upper bound on
  the maximum number of frames needed as well.

  <subsubsection|Maximum Cell Count Bound>

  We define the cell count of a frame to be the length of its underlying cell
  array and the cell count of a Bit Machine state to be the sum of the cell
  counts of all its frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|cellCount<around*|(|<carr|c<rsub|1>\<cdots\><wide*|c<rsub|i>|\<bar\>>\<cdots\>c<rsub|n>>|)>>|<cell|\<assign\>>|<cell|n>>|<row|<cell|cellCount<around*|(|<around*|[|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>|]>|)>>|<cell|\<assign\>>|<cell|<big|sum><rsup|n><rsub|i=0>cellCount<around*|(|r<rsub|i>|)>+<big|sum><rsup|m><rsub|j=0>cellCount<around*|(|w<rsub|j>|)>>>>>
  </eqnarray*>

  Given a trace of execution of a Bit Machine program <math|p> from an
  initial state <math|S<rsub|0>> to a final state <math|S<rsub|1>>, <math|p :
  S<rsub|0>\<twoheadrightarrow\>S<rsub|1>>, we define the cells required by
  this execution as the cell count of every intermediate state.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>|<row|<cell|<math|cellsReq<around*|(|i|)><rsub|>\<assign\>
    max<around*|(|cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>,cellCount<around*|(|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|k<rsub|0>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>|<cell|<math|k<rsub|1>
    : <around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>>>>>>|<row|<cell|<math|cellsReq<around*|(|k<rsub|0>;k<rsub|1>|)>\<assign\>max<around*|(|cellsReq<around*|(|k<rsub|0>|)>,cellsReq<around*|(|k<rsub|1>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|k<rsub|0>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>|<row|<cell|<math|cellsReq<around*|(|k<rsub|0><around*|\|||\|>k<rsub|1>|)><rsub|>\<assign\>cellsReq<around*|(|k<rsub|0>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|k<rsub|1>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|''>\<vartriangleright\>r<rsub|0><rprime|''>\|w<rsub|0><rprime|''>\<vartriangleleft\>\<Xi\><rprime|''>|]>>>>|<row|<cell|<math|cellsReq<around*|(|k<rsub|0><around*|\|||\|>k<rsub|1>|)><rsub|>\<assign\>cellsReq<around*|(|k<rsub|1>|)>>>>>>>
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
    For any Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <around*|\<llangle\>|t|\<rrangle\>>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<around*|\<llangle\>|t|\<rrangle\>>:<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>+extraCellsBound<around*|(|t|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <around*|\<llangle\>|t|\<rrangle\>>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<around*|\<llangle\>|t|\<rrangle\>>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<around*|(|t|)>>.
  </lemma>

  We can compute a tighter bound for TCO translation, but the calculation is
  a bit more complicated. \ The number of extra cells needed depends on
  whether TCO is in the ``on'' state, and what the size of the active read
  frame is.

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
    For any Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <TCOon|t><rsup|>:<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>
    </equation*>

    and

    <\equation*>
      <TCOoff|t><rsup|>:<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>=cellCount<around*|(|r<rsub|on,0>|)>+cellCount<around*|(|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>|)>>
      and<next-line><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<TCOon|t>:<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|cellCount<around*|(|r<rsub|on,0>|)>|)>>
      and<next-line><math|cellsReq<around*|(|<TCOoff|t><rsup|>:<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>\<twoheadrightarrow\><around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <TCOoff|t>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<TCOoff|t>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)><text|.>>
  </lemma>

  The problem with <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>
  is that it is effectively a dynamic analysis because its result is a
  function. We cannot direclty use this definition to perform a static
  analysis because we cannot cache and reuse results on shared
  sub-expressions. \ Fortuantely we can charaterize the set of possible
  functions returned by <math|extraCellsBound<rsup|TCO><rsub|dyn>> by a pair
  of parameters.

  <\equation*>
    interp<rsup|TCO><around*|\<langle\>|n,m|\<rangle\>><around*|(|r|)>\<assign\>max<around*|(|n-r,m|)>
  </equation*>

  We can write a static analysis to compute the pair of parameters that
  characterize the results of \ <math|extraCellsBound<rsup|TCO><rsub|dyn>>.

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
    For any Simplicity expression <math|t:A\<vdash\>B> and <math|a:A> such
    that

    <\equation*>
      <TCOoff|t>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <\equation*>
      cellsReq<around*|(|<TCOoff|t>:<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>\<twoheadrightarrow\><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+max<around*|(|n,m|)><text|>
    </equation*>

    where <math|<around*|\<langle\>|n,m|\<rangle\>>\<assign\>><math|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>.
  </corollary>

  <subsubsection|Maximum Frame Count Bound>

  <subsection|Time Resources>

  <subsection|Commitment Merkle Root>

  <section|Serialization>

  <subsection|Type Inference>

  <chapter|Full Simplicity>

  <section|Assertions>

  <subsection|Salted Expressions>

  <section|Witness Merkle Root>

  <section|Oracles>

  <subsection|Hidden Salted Expressions>

  <subsection|Serialization with Oracles>

  <subsection|Type Inference with Oracles>

  <section|Blockchain Primitives>

  <subsection|Bitcoin Transactions>

  <subsection|Schnorr Signature Aggregation>

  <section|Malleability>

  <subsection|Transaction Weight>

  <chapter|Jetted Simplicity>

  <section|Example: The Standard Single Signature>

  <chapter|Extended Simplicity>

  <section|Disconnect>

  <chapter|Coq Library Guide>

  The Coq development for Simplicity is found in the <verbatim|Coq/>
  directory. \ There are two subdirectories, <verbatim|Simplicity/> contains
  modules releated to Simplicity, and the <verbatim|Util/> directory has a
  few modules dedicated to other structures that are not specific to
  Simplicity, but that we will make use of in the Simplicity development.
  \ We will focus on the contents of the <verbatim|Simplicity/> directory.

  <section|Simplicity Types>

  The Coq development for Simplicity begins with the
  <verbatim|Simplicity/Ty.v> file. \ This contain the inductive definition of
  <verbatim|Ty> which defines Simplicity's type expressions. \ The
  <verbatim|tySem> function interprets Simplicity types as Coq types, and it
  is declared as coercion. \ The module also provides standard arithmetic
  notation for Simplicity's sum and product types.

  <section|Simplicity Terms>

  There are two different representations of Simplicity terms defined in Coq.
  \ One representation is an ``inital'' representation, as an inductive
  types. \ The other representation is a ``final'' representation, as based
  on algebras (see <hlink|F-algebra|https://en.wikipedia.org/wiki/F-algebra>)
  for Simplicity.

  Generally speaking we use the ``initial'' representation when reasoning
  about Simplicity programs to prove properties about them, and we use the
  ``final'' representation when creating specific Simplicity programs.

  We begin with the ``initial'' represetation, which will most readers will
  find more familiar.

  <subsection|The ``Initial'' Representation of Terms>

  The <verbatim|Simplicity/Core.v> module defines an inductive family,
  <verbatim|Term A B>, for the well-typed core Simplicity language. \ The
  core language is the pure fragment of Simplicity that has no effects such
  as failure or read access to the transaction environment. \ The
  <verbatim|eval> function provides denotational semantics and interprets
  terms as Coq functions over the corresponding Coq types.

  This module also establishes the Core Simplicity completeness theorem
  (Theorem <reference|thm:CSCT>) as the <verbatim|Simplicity_Completeness>
  theorem. \ The proof is built from <verbatim|scribe>, a function to produce
  Simplicity terms representing constant functions, and <verbatim|reify>
  which transforms Coq functions over Simplicity types into Simplicity terms
  representing those functions.

  <with|color|red|TODO: non-core Simplicity terms>

  <subsection|The ``Final'' Representation of Terms>

  To explain the ``final'' representation of terms it is first neccessary to
  understand what an algebra for Simplicity is. We can understand this by way
  of a mathematical analogy with ring theory. A ring is a mathematical
  structure consiting of a domain along with constants from that domain that
  correspond to 0 and 1, and binary functions over that domain that
  correspond to <math|\<noplus\>+> and <math|\<times\>> operations that
  satify certain ring laws. \ A term from the language of rings is an
  expression made out of <math|0>, <math|1>, <math|+>, and <math|\<times\>>.
  \ Given a ring and a term from the langauge of rings, we can intepret that
  term in the given ring and compute an element of the domain that the term
  represents. \ There are many different rings structures, such as the ring
  of integers, and the ring of integers modulo <math|n> for any positive
  number <math|n>. \ A given term can be interpreted as some value for any
  ring. It turns out that an alternative way to represent terms is as a
  function that given any ring returns a value from its domain and does so in
  a ``uniform'' way. \ This would be the ``final'' representation for terms
  in the langauge of rings.

  <subsubsection|Simplicity Algebras>

  An algebra for Simplicity is an analgous structure to a ring. \ An algebra
  for Simplicity consists of a domain, along with constants from that domain
  that correspond to <math|<math-ss|iden>> and <math|<math-ss|unit>> and
  functions over that domain that correspond the other combinators from
  Simplicity. \ Unlike the case for rings, the domain of a Simplicity algebra
  is indexed by a pair of Simplicity types, and naturally the constants and
  functions that interpret Simplicity combinators must respect these types
  (and unlike rings, we are not going to impose any extra laws, making it a
  free-algebra).

  Simplicity algebras are formalized in the <verbatim|Simplicity/Alg.v> file.
  \ The <verbatim|Core.Class.class> record captures the interpretation of
  constants and combinators for core Simplicity over a given domain. \ The
  <verbatim|Core.Algebra> structure is the type of Simplicity algebras,
  containing a type family for the domain, and an instance of the
  <verbatim|Core.Class.class> record for interpretations.

  Given any Simplicity algebra and a well-typed term (from the ``initial''
  representation) we can interpret that term in the algebra to get out a
  value from the domain (that has a type corresponding to the type of the
  term). \ The <verbatim|Core.eval> function performs this interpretation by
  recursively evaluating the interpretation of the core Simplicity
  combinators from the algebra.

  What sort of Simplicity algebras are there? The most obvious one is the
  functional semantics of Simplicity. \ The domain of this algebra is the
  functions between Simplicity types. \ This domain is indexed by the input
  and output Simplicity types. \ The interpretation of the
  <math|<math-ss|iden>> and <math|<math-ss|unit>> constants are the idenity
  and constant-unit functions respectively and the intepretation of the other
  core Simplicity combinators is also in accordance with Simplicity's
  denotational semantics. \ This algebra is defined in the <verbatim|CoreSem>
  structure and the <verbatim|CorSem_correct> lemma proves that the
  interpretation of terms in the ``initial'' representation into this algebra
  results in the same function that the <verbatim|eval> function from
  <verbatim|Simplicity/Core.v> produces. \ The <verbatim|\|[ x ]\|> notation
  denotes this denotation semantics using the <verbatim|CoreSem> domain.

  Another example of a Simplicity algebra is the ``initial'' reprsentation of
  terms themselves, which form a trivial algebra. \ This domain of Simplicity
  terms is also indexed by input and output Simplicity types and the
  constants and combinators are interpreted as themselves. \ This algebra is
  defined in the <verbatim|Core.Term> structure and the
  <verbatim|Core.eval_Term> lemma proves that the interpretation of any term
  in this algebra returns the original term back.

  There are several other Simplicity algebras. Programs for the Bit Machine
  form a Simplicity algebra with the translation from Simplicity to Bit
  Machine code defining the interpreptation of core Simplicity combinators.
  \ Also 256-bit hashes are a Simplicity algebra with the merkle root
  computation defining the interpretation of core Simplicity combinators.
  \ Static analysis of resource usage for Simplicity expressions will for yet
  another set of Simplicity algebras.

  <subsubsection|The ``Final'' Representation>

  The ``final'' representation of a Simplicity term is as a function that
  selects a value out of any Simplicity algebra and does so in a ``uniform''
  manner. \ A ``uniform'' manner means a function that satifies the
  <verbatim|Core.Parametric> property which effectively says that that the
  values choosen by the function from two domains must each be constructed
  from a composition of the intepretation of combinators in the two domains
  in the same way. \ In other words, the function must act the the
  intepretation of some ``inital'' represented term under
  <verbatim|Core.eval> for any domain.

  Terms in the ``inital'' representation can be converted to the ``final''
  representation by parital application of <verbatim|Core.eval>. \ The
  <verbatim|Core.eval_Parametric> lemma proves that the resulting ``final''
  representation resulting from <verbatim|Core.eval> satisfies the
  <verbatim|Core.Parametric> property.

  Terms in the ``final'' representation can be converted into the ``initial''
  representation by applying the function to the <verbatim|Core.Term>
  Simplicity algebra. \ The <verbatim|Core.eval_Term> lemma shows that
  converting from the ``initial'' representation to the ``final''
  representation and back to the ``initial'' representation returns the
  original value. \ The <verbatim|Core.term_eval> lemma shows that starting
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
  the hint database as they create new Simplicity expressions. \ Some
  examples of this can be found in the <verbatim|Simplicity/Arith.v> module.

  <subsection|Why two representations of Terms?>

  The ``initial'' inductive representation is the traditional definition one
  expects for terms and is easy to reason inductively about. \ This is the
  representation we will typically use in proofs. \ The problem with this
  representation is that, due to lack of sharing between sub-expressions, it
  is expensive to evaluate with these terms inside Coq itself. \ For example,
  one cannot compute Merkle roots of anything but the most trivial of
  expressions.

  The ``final'' algebra representation solves this problem by allowing
  transparent sharing of expressions. In the ``final'' representation, terms
  are really values of a Simplicity algebra. When these values are shared
  using in Coq's let expressions, or shared via some function argument in
  Coq, those values of the algebra are shared during computation within Coq.
  This representation makes it feasable to acutally compute Merkle roots for
  Simplicity expressions directly inside Coq.

  Both representations are used throughout the Simplicity Coq library. \ The
  ``final'' representation is used when building concrete Simplicity
  expressions. \ The ``initial'' representation is used when reasoning about
  functions of Simplicity expressions. \ The isomorphism between the two
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
  <verbatim|'Bit.one'>. \ The Simplicity expressions <verbatim|false> and
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
  types of finite words. \ The class provides <verbatim|toZ> and
  <verbatim|fromZ> operations that convert between standard Coq integers and
  these types of finite words along with proofs that the conversion functions
  are inverses modulo the word size. \ <verbatim|Canonical Structure>
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
  <math|2<rsup|n>>-bit word result. \ The <verbatim|multiplier> expression
  defines the product of two <math|2<rsup|n>>-bit word and returns a
  <math|2<rsup|n+1>>-bit word. \ The <verbatim|fullMultiplier> expression
  takes a quadruple, <math|<around*|(|<around*|(|a,b|)>,<around*|(|c,d|)>|)>>
  of <math|2<rsup|n>>-bit words and returns <math|a\<cdot\>b+c+d> as a
  <math|2<rsup|n+1>>-bit word.

  Each of these expressions has an associated correctness lemma. \ These
  expressions are all defined in the ``final'' representation and there are
  parametricity lemmas for each expression.

  <section|The Bit Machine>

  The <verbatim|Simplicity/BitMachine.v> file provides the primary definition
  of the abstract Bit Machine. This definition, and hence this file, is
  independent of the rest of the Simplicity language.

  The <verbatim|Cell> type explicity tracks cell values in the bit machien as
  being one of <verbatim|0>, <verbatim|1>, and undefined. \ <verbatim|None>
  represents the undefined value and <verbatim|Some false> and <verbatim|Some
  true> represent <verbatim|0> and <verbatim|1> respectively.

  The <verbatim|ReadFrame> record represents read frames. \ It uses a zipper
  representation of a list with a cursor: The elements of the list in front
  of the cursor are in the <verbatim|nextData> field and the elements of the
  list behind the cursor are in the <verbatim|prevData> field stored in
  <em|reverse order>. \ The <verbatim|setFrame> function builds a read frame
  from a list with the cursor set to the beginning of the frame.

  The <verbatim|WriteFrame> record represents write frames. \ It uses a
  similar zipper representation where the <verbatim|writeData> field holds
  the elements behind the cursor in <em|reverse order>. \ Because write
  frames are append only, every cell in front of the cursor must be an
  undefined value. For this reason we only store the number of cells in front
  of the cursor in the <verbatim|writeEmpty> field. \ The
  <verbatim|newWriteFrame> function builds an empty write frame of a given
  size and the <verbatim|fullWriteFrame> function builds an filled write
  frame from a list.

  The <verbatim|State> record represents the state of the Bit Machine. \ It
  consists of

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

  It is sometimes useful to decompose the Bit Machine's state as\ 

  <\equation*>
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n<rsub|0>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><cearr|c<rsub|1>\<cdots\>c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  where we are locally interested in what is immediately in front of the
  active read frame's cursor, <math|<carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n<rsub|0>>>>,
  and what is immediately surrounding the active write frame's cursor,
  <math|<cearr|c<rsub|1>\<cdots\>c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>>>.
  \ This is captured by the <verbatim|LocalState> type, noting that the data
  immediately surrounding the active write frame's cursor is captured by the
  <verbatim|WriteFrame> type. \ The remainder of the state, consisting of
  <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|>\<bullet\>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\>\<bullet\>\<cdummy\><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
  is captured by the <verbatim|Context> type, which happens to be isomorphic
  to the <verbatim|State> type. \ The <verbatim|fillContext> function
  combines a <verbatim|Context> value and a <verbatim|LocalState> value to
  build a complete <verbatim|State> value.

  Sometimes we are intersted in of some <verbatim|LocalState> within another
  <verbatim|LocalState>. \ The context of such a decomposition is isomorphic
  to <verbatim|LocalState> and we don't even both giving a type alias to
  this. The <verbatim|appendLocalState> funciton combines a context,
  <verbatim|ls1>, with a <verbatim|LocalState>, <verbatim|ls2>, to build a
  combined <verbatim|LocalState>. <verbatim|appendLocalState> makes
  <verbatim|<verbatim|LocalState>> into a monoid and <verbatim|fillContext>
  becomes a monoid action on <verbatim|Context>s with respect to this monoid.
  This theory isn't fully developed in Coq, but will be if it is needed. The
  <verbatim|context_action> lemma proves the monoid action property, which is
  the only theorem needed so far.

  <subsection|Bit Machine Code>

  The <verbatim|MachineCode.T <em|S1> <em|S2>> type is an enumeration of the
  nine primary instructions of the Bit Machine. The type of these
  instructions are parameterized by the legal states that the instructions
  can successfully operate in, <verbatim|<em|S1>>, and the resulting state
  after execution of the instruction, <verbatim|<em|S2>>. In this way, the
  <verbatim|MachineCode.T> type family represents a precategory (also known
  as a directed graph) that captures the machine instructions and their
  semantics. \ There is an objects (a.k.a. node) for every possible state of
  the Bit Machine. \ There is an arrow (a.k.a. edge) between two states if
  there is an instruction of the Bit Machine that successfully transitions
  from the source state to the target state, and that arrow (a.k.a. edge) is
  labled with the name of the instruction. The specific type
  <verbatim|MachineCode.T <em|S1> <em|S2>> is the type of all instructions
  that transition from state <verbatim|<em|S1>> to state <verbatim|<em|S2>>.
  The <verbatim|crash> instruction is never successful, and thus never
  appears in the precategory (a.k.a. directed graph). This is why it doesn't
  occur in the <verbatim|MachineCode.T> type family.

  A thrist of <verbatim|MachineCode.T> is the free category generated from
  the precategory <verbatim|MachineCode.T>. This free category can also be
  understood as a collection of all paths through the directed graph of all
  machine instructions and their associated state transitions. The specific
  type <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> is the type of all
  sequences of instructions that transition from state <verbatim|<em|S1>> to
  state <verbatim|<em|S2>>. \ This type captures the semantics of sequences
  of machine instructions.

  The notation <verbatim|<em|S1> ~~\<gtr\> <em|S2>> denotes the
  <verbatim|MachineCode.T <em|S1> <em|S2>> type of single step transitions,
  which corresponds to <math|S<rsub|1>\<rightsquigarrow\>S<rsub|2>>. \ The
  notation <verbatim|<em|S1> -\<gtr\>\<gtr\> <em|S2>> denotes the
  <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> type of multi-step
  (including 0 step) transitions between states <verbatim|<em|S1>> and
  <verbatim|S2> and the trace of the instructions used, which corresponds to
  <math|S<rsub|1>\<twoheadrightarrow\> S<rsub|2>>.

  <subsubsection|Bit Machine Programs>

  We interpret a Bit Machine <verbatim|Program> as a function taking an
  initial machine state and, if successful, returning a final machine state
  along with a thrist of machine instructions that connect the initial state
  to the final state. For each machine instruction, we define a simple
  <verbatim|Program> that tries to execute that single instruction once and
  returns that state transition. \ If the initial state given to these single
  instruction programs isn't valid for their instruction, the program fails
  by returning <verbatim|None>. \ Most of these single instruction programs
  have an associated correctness lemma that proves they run successfully when
  run from an initial state valid for their instruction. \ We also define a
  <verbatim|crash> program, which always fails, and the trivial
  <verbatim|nop> program that contains no instructions.

  These single instruction programs can be combined into more complex
  programs using the <verbatim|seq> and <verbatim|choice> combinators. \ The
  <verbatim|seq> combinator sequences two programs, running the second
  program starting from the final state of the first program and combines
  their thrists. The sequence fails if either program fails. The
  <verbatim|choice> combinator picks between running two programs by peeking
  at the cell immedately after the active read frame's cursor from the
  initial state and running either the first or second program depending on
  whether the cell holds a <verbatim|0> or <verbatim|1> value. If the cell
  holds an undefined value, or if the active read frame's cursor is at the
  end of the frame, the <verbatim|choice> combinator fails. \ The notations
  <verbatim|<em|k0> ;;; <em|k1>> and <verbatim|<em|k0> \|\|\| <em|k1>> denote
  the sequence and choice combinations respectively of two programs and
  correspond to <math|k<rsub|0>;k<rsub|1>> and
  <math|k<rsub|0><around*|\|||\|>k<rsub|1>>. We also define the combinator
  <verbatim|bump <em|n> <em|k>> which corresponds to <math|n\<star\>k>.

  The <verbatim|runMachine> function takes a <verbatim|Program> and an
  initial <verbatim|State> and extracts the resulting final <verbatim|State>
  if the program is sucessful. For denotational semantics we only care about
  the resulting final state. For operational semantics we will care how we
  got there. \ A few lemmas are provided to help reason about the behaviour
  of <verbatim|runMachine> when running the program combinators.

  The <verbatim|maximumMemoryResidence> function computes the maximum number
  of cells used by any intermediate state from the trace of execution of a
  Bit Machine program. <verbatim|programMaximumMemoryResidence> runs a given
  program from a given initial state and returns the
  <verbatim|maximumMemoryResidence> of the resulting trace. \ A few lemmas
  are provided to help reason about the behaviour of
  <verbatim|programMaximumMemoryResidence> when running the program
  combinators.

  <subsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Simplicity/Translate.v> file defines how to transform
  Simplicity programs into Bit Machine programs that perform the same
  computation. The <verbatim|bitSize> and <verbatim|encode> functions
  implement <math|bitSize<around*|(|A|)>> and <math|<rep|a|A>> respectively.

  The <verbatim|Naive.translate> structure provides a Simplicity algebra for
  Bit Machine <verbatim|Progam>s that interprets Simplicity terms according
  to the naive translation. The <verbatim|Naive.translate_correct> theorem is
  actually a function that produces a thrist of Bit Machine instructions that
  transform suitable initial machine states that contain an encoding of
  Simplicity function's input to suitable final machine states that contain
  an encoding of Simplicity function's output (and input). The
  <verbatim|translate_correct> theorem also proves that this thrist is the
  ouput of evaluating the <verbatim|Program> generated by the
  <verbatim|Naive.translate> Simplicity algebra. The <verbatim|spec> property
  defines an inductive hypothesis that is used by
  <verbatim|Naive.translate_spec> that makes up the heart of this proof.

  The <verbatim|Naive.translate_correct_parametric> theorem is a variation of
  the <verbatim|Naive.translate_correct> theorem. \ The
  <verbatim|Naive.translate_correct> operates on Simplicity term in the
  ``initial'' representaiton whereas the <verbatim|Naive.translate_correct_parametric>
  theorem operates on Simplicity terms in the ``final'' representation.

  <subsection|Static Analysis>

  The <verbatim|Simplicity/StaticAnalysis.v> files defines the static
  analyses of Simplicity program that compute bounds on the various
  computational resources used by the Bit Machine when executing translated
  Simplicity. \ The file also proves the correctness of these upper bounds.

  The <verbatim|MaximumMemory> module defines the
  <verbatim|MaximumMemory.extraMemoryBound> algebra which is used to compute
  an upper bound on additional memory that will be used when Simplicity
  sub-expressions are naively translated to the Bit Machine and executed.
  \ The <verbatim|MaximumMemory.Core_spec> lemma proves that for naively
  translated core Simplicity expressions, the maximum memory used by the Bit
  Machine is the memory needed by the size of the initial state, plus the
  results of <verbatim|MaximumMemory.extraMemoryBound>. \ This bound holds no
  matter what the starting state is, even if it is not a valid state for
  holding the input for the Simplicity expression.

  The <verbatim|MaximumMemory.CellBound> function computes the memory used by
  the Bit Machine for evaluating Simplicity expressions starting from a
  standard initial state and <verbatim|MaximumMemory.CellBound_correct>
  proves that this upper bound is correct.

  <chapter|Haskell Library Guide>

  WARNING: \ None of the Haskell library development is normative. \ There is
  no formalized connecton between any of the Haskell library and Simplicity's
  formal semantics and development in Coq. There could be errors in the
  Haskell library that cause it to disagree with the formal development
  defined in Coq. \ This library is intended to be used for experimental,
  exporitory and rapid development of Simplicity related work, but should not
  be relied upon for production development. \ For production development,
  formal developments in Coq should be done.

  The Haskell development for Simplicity is found in the <verbatim|Haskell>
  directory. \ The <verbatim|Haskell/Tests.hs> file imports the various test
  modules throught the development to build a testing executable to run them
  all.

  <section|Simplicity Types>

  The <verbatim|Simplicity/Ty.hs> file contains the development of Simplicity
  types. \ There are three different ways that Simplicity types are captured
  in Haskell.

  The primary way Simplicity types are captured is by the <verbatim|TyC>
  class which only has instances for the Haskell types that correspond to the
  Simplicity types:

  <\itemize-dot>
    <item><verbatim|instance TyC ()>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (Either a b)>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (a, b)>
  </itemize-dot>

  \ The <verbatim|TyC> class is crafted so that is methods are not exported.
  \ This prevents anyone from adding further instances to the <verbatim|TyC>
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
  \ For each Haskell type corresponding to a Simplicity type, <verbatim|a>
  the <verbatim|TyReflect a> type has exactly one value that is built up out
  of other values of type <verbatim|TyReflect> corresponding to the
  Simplicity type sub-expression. \ For example the value of type
  <verbatim|TyReflect (Either () ())> is <verbatim|SumR OneR OneR>.

  The <verbatim|reify :: TyC a =\<gtr\> TyReflect a> uses the one method of
  the <verbatim|TyC> class to produce the value of the <verbatim|TyReflect>
  GADT that corresponds to the type constrained by the <verbatim|TyC>
  constraint. When users have a Haskell type constrained by <verbatim|TyC>
  they can use <verbatim|reify> to get the corresponding concrete value of
  the <verbatim|TyReflect> GADT which can then be further processed. \ The
  <verbatim|reifyProxy> and <verbatim|reifyArrow> functions are helper
  functions for <verbatim|refiy> that let you pass types via a proxy.

  The third way Simplicity types are captured is by the <verbatim|Ty> type
  alias, which is the fixed point of the <verbatim|TyF> functor. \ This is a
  representation of Simplicity types as a data type. \ The <verbatim|one>,
  <verbatim|sum>, and <verbatim|prod> functions provide smart-constructors
  that handle the explicit fixpoint constructor.

  Generally speaking, we will use <verbatim|TyC> to constrain Haskell types
  to Simplicity types when creating Simplicity expressions. \ This way
  Simplicty type errors are also Haskell type errors and can be caught by the
  Haskell compiler. \ We use the <verbatim|Ty> type when doing compuation
  like deserializing Simplicity expressions and performing unification for
  Simplicity's type inference. The <verbatim|TyReflect> GADT links these two
  representations. \ For example, the <verbatim|equalTyReflect> function can
  test if two Simplicity types are equal or not, and if they are equal then
  it can unify the Haskell type variables that represent the two Simplicity
  types. \ The <verbatim|unreflect> function turns a <verbatim|TyReflect>
  value into a <verbatim|Ty> value by forgetting about the type parameter.

  <section|Simplicity Terms>

  The <verbatim|Simplicity/Term.hs> file contains the development of
  Simplicity terms. \ We do not provide a data type represenation of terms.
  \ Instead terms are represented in tagless-final
  style<inactive|<cite|<with|color|red|TODO>>>. This style is analgous to the
  ``final'' represention of terms that is defined in the Coq library. \ The
  <verbatim|Core> type class captures Simplicity algebras for core Simplicity
  expressions. \ Core Simplicity expressions are represented in Haskell by
  expressions of type <verbatim|Core term =\<gtr\> term a b> which are
  expressions that hold for all Simplicity algebras. \ Haskell's
  parametricity implicity implies the parametricity conditions that is
  explicitly required in the Coq development's ``final'' representation.

  The primary purpose of using tagless-final style is to support transparent
  sharing of subexpressions in Simplicity. While subexpressions can be shared
  if we used a GADT to represent Simplicity terms, any recursive function
  that consumes such a GADT cannot take advantage of that sharing. Sharing
  results of static analysis between shared sub-experssions is critical to
  making static analysis practical. Adding explicit sharing to the Simplicity
  language would make the langauge more complex and would risk incorrectly
  implementing the sharing combinator. \ Explicitly building memoization
  tables could work, but will have overhead. \ The solution of using
  tagless-final style lets us write terms in a natural manner and we get
  sharing for Simplicity expressions at exactly the points where we have
  sharing in the Haskell representation of Simplicity.

  This module provides infix operators, <verbatim|(\<gtr\>\<gtr\>\<gtr\>)>
  and <verbatim|(&&&)>, for the <verbatim|comp> and <verbatim|pair>
  Simplicity combinators respectively. \ It also provides notation for short
  sequences of string of <samp|I>'s, <samp|O>'s and <samp|H>'s. Note that
  because <verbatim|case> is a reserved word in Haskell we use
  <verbatim|match> for Simplicty's <samp|case> combinator. Examples of
  building Simplicity expressions can be found in the next section.

  This module provides a <verbatim|Core (-\<gtr\>)> instance that provides
  the denotational semantics of Simplicity expressions; one can take core
  Simplicity term and directly use them as functions.

  <section|Example Simplicity Expressions>

  The <verbatim|Simplicity/Programs> directory contains various developments
  of Simplicity expressions in Haskell. \ The
  <verbatim|Simplicity/Programs/Tests.hs> has some Quickcheck properties that
  provide randomized testing for some of the programs defined in this
  section.

  <subsection|Bits>

  The <verbatim|Simplicity/Programs/Bit.hs> file has Simplicity expressions
  for bit manipulation. In Simplicity the <verbatim|Bit> type is represented
  as <verbatim|Either () ()>, while in Haskell we usually use the
  <verbatim|Bool> type. \ The <verbatim|fromBit> and <verbatim|toBit>
  functions provide the canonical isomorphisms between these two types.
  \ <verbatim|false> and <verbatim|true> are Simplicity expressions for the
  constant functions of those types and <verbatim|cond> provides case
  analysis combinator for a single bit. \ There are combinators for various
  logical operators. These logical operators are short-circuted where
  possible. \ There are also a few trinary boolean Simplicity expressions
  that are used in hash functions such as SHA-256.

  <subsection|Multi-bit Words>

  The <verbatim|Simplicity/Programs/Word.hs> file provides support for
  multi-bit word Simplicity types and Simplicity expressions that operate on
  these word types.

  The <verbatim|Word> GADT describes Simplicity types for multi-bit words.
  Its type parameter is restricted to either be a single <verbatim|Bit> word
  type or a product that doubles the size of a previous word type. \ The
  <verbatim|wordTy> functions transforms a <verbatim|Word> GADT to the
  corresponding <verbatim|TyReflect> GADT. \ The <verbatim|wordSize> returns
  the number of bits a word has. \ The <verbatim|fromWord> and
  <verbatim|toWord> functions convert values of Simplicity words types to and
  from Haskell <verbatim|Integer>s (modulo the size of the word). \ The file
  also provides specializations of these various functions for popular word
  sizes between 8 and 256 bits.

  <subsubsection|Arithmetic operations>

  The <verbatim|Simplicity/Programs/Word.hs> file also provides the standard
  implemenations of the <verbatim|zero>, <verbatim|adder>,
  <verbatim|fullAdder>, <verbatim|multiplier>, and <verbatim|fullMultiplier>
  Simplicity expressions. Notice that the implementation of these functions
  is careful to use explicit sharing of Simplicity sub-expressions where
  possible through the <verbatim|where> clauses.

  <subsubsection|Bit-wise operations>

  The <verbatim|shift> and <verbatim|rotate> functions create Simplicity
  expressions that do left shifts and rotates of multi-bit words by any
  constant amount. \ Right (unsigned) shifts and rotates can be made by
  passing a negative value for the shift/rotate amount.

  The <verbatim|bitwise> combinator takes a Simplicity expression for a
  binary bit operation and lifts it to a Simplicity expression for a binary
  operation on arbitrary sized words that performs the bit operation
  bit-wise. \ There is also a variant, called <verbatim|bitwiseTri> the does
  the same thing for trinary bit operations.

  <subsection|Generic>

  The <verbatim|Simplicity/Programs/Generic.hs> file provides some Simplicity
  expressions that can apply to any Simplicity type.

  The <verbatim|scribe> function produces a Simplicity expression denoting a
  constant function for any value for any Simplicity type. \ The
  <verbatim|eq> Simplicity expression compares any two values of the same
  Simplicity type and deicides if they are equal or not.

  <subsection|SHA-256>

  The <verbatim|Simplicity/Programs/Sha256.hs> files provides Simplicity
  expressions to help compute SHA-256 hashes. \ The <verbatim|iv> Simplicity
  expression is a constant function the returns the initial value to begin a
  SHA-256 computation. \ The <verbatim|hashBlock> Simplicity expression
  computes the SHA-256 compression function on a single block of data. To
  compress multiple blocks, multiple calls to the <verbatim|hashBlock>
  function can be chained together.

  <section|The Bit Machine>

  The <verbatim|Simplicity/BitMachine/> directory has modules related to the
  Bit Machine and evaluation of Simplicity via the Bit Machine.

  The <verbatim|Simplicity/BitMachine/Ty.hs> file defines <verbatim|bitSize>,
  <verbatim|padL>, and <verbatim|padR>, which define the <math|bitSize>,
  <math|padR> and <math|padL> functions from
  Section<nbsp><with|color|red|TODO>. \ They operate on the <verbatim|Ty>
  type. \ The file also defines variants of these three function that operate
  on the <verbatim|TyReflect> GADT instead.

  The <verbatim|Simplicity/BitMachine.hs> file (technically not in the
  <verbatim|Simplicity/BitMachine/> directory) defines the canonical type of
  a <verbatim|Cell> to be a <verbatim|Maybe Bool>, with the
  <verbatim|Nothing> value representing undefined cell values. \ The
  <verbatim|encode> and <verbatim|decode> functions transform a value of a
  Simplicity type to and from a list of <verbatim|Cell>s that represent the
  value. \ The <verbatim|executeUsing> combinator captures a common pattern
  of running a Simplicity program through an implementation of the Bit
  Machine by encoding program inputs and decoding the results. \ Since there
  is more than one way to compile and run Simplicity program on the Bit
  Machine (for example, see naive translation versus TCO translation), this
  abstraction is used is multiple places.

  The <verbatim|MachineCode> type alias captures canonical forms of programs
  for the Bit Machine, which is the explicit fixed point of the
  <verbatim|MachineCodeF> functor. \ Usually programs are built in
  continuation passing style (analogous to using difference lists to build
  lists), making use of the <verbatim|MachineCodeK> type alias. There are
  smart-constructors for each machine code that make single instruction
  <verbatim|MachineCodeK> programs. \ Programs are composed sequentually
  using ordinary function compostion, <verbatim|(.)>. \ Determinic choice
  between two programs is provided by the <verbatim|(\|\|\|)> operator. \ The
  <verbatim|nop> program is an alias for the identity function.

  The <verbatim|Simplicity/BitMachine/Authentic.hs> file is an implementation
  of the Bit Machine that follows the formal definition of the Bit Machine
  and fully tracks undefined values. \ The <verbatim|Frame> type is used for
  both read frames and write frames. \ The <verbatim|Active> type is captures
  the pair of active read and write frames, and the <verbatim|State> type
  captures the entire state of the Bit Machine. \ Lenses are used to access
  the components of the State.

  The <verbatim|runMachine> function interprets <verbatim|MachineCode> in
  accorance with the semantics of the Bit Machine, and transforms an initial
  state into a final state (possibly crashing during execution). \ It is
  meant to be used, in conjunction with a Simplicity translator, with
  <verbatim|executeUsing>. \ The <verbatim|instrumentMachine> function is a
  variant of <verbatim|runMachine> that logs statistics about memory usage
  during the execution. \ It is used as part of the testing for static
  analysis.

  <subsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Simplicity/BitMachine/Translate.hs> file defines the naive
  translation from Simplicity to the Bit Machine. \ The
  <verbatim|Translation> type wraps the <verbatim|MachineCodeK> type with
  phantom type parameters in order to make an instance suitable for a
  Simplicity Algebra. \ The <verbatim|translate> function translates
  Simplicity terms to Machine Code via the <verbatim|Translation> Algebra
  (recall that a Simplicity term in tagless final form is a polymorphic value
  that can become any Simplicity Algebra). The
  <verbatim|Simplicity/BitMachine/Translate/TCO.hs> file provides a similar
  <verbatim|Translation> Simplicity Algebra and <verbatim|translate>
  functions, but this translating using tail composition optimization.

  The <verbatim|Simplicity/BitMachine/Tests.hs> runs a few of the example
  Simplicity expressions through the Bit Machine implementation to test that
  the value computed by the Bit Machine matches that direct interpretation of
  the same Simplicity expressions. \ In this file you can see an example of
  how <verbatim|executeUsing (runMachine . translate) program> is used.

  <subsection|Static Analysis>

  The <verbatim|Simplicity/BitMachine/StaticAnalysis.hs> file performs the
  static analysis for bounding the maximum number of cells used by the Bit
  Machine when executing the naive translation of Simplicity expressions.
  \ The <verbatim|ExtraCellsBnd> type wraps the data needed for the static
  analysis with phantom type parameters in order ot make an instance suitable
  for a Simplicity Algebra. \ The <verbatim|cellsBnd> function computes the
  bound on cell use from Simplicity terms via the <verbatim|ExtraCellsBnd>
  Algebra. The <verbatim|Simplicity/BitMachine/StaticAnalysis/TCO.hs> file
  provides a similar static analysis that bounds the maximum number of cells
  used by the Bit Machine when executing the TCO translation of Simplicity
  expressions.

  The <verbatim|Simplicity/BitMachine/StaticAnalysis/Tests.hs> runs a few of
  the example Simplicity expressions through the static analysis and compares
  the result with the maximum cell count of executing the Bit Machine on
  various inputs. In this file you can see an example of how
  <verbatim|executeUsing (instrumentMachine . translate) program> is used.

  <chapter|C Library Guide>
</body>

<\initial>
  <\collection>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|LC218|<tuple|6.2.2|?>>
    <associate|LC219|<tuple|<with|mode|<quote|math>|\<bullet\>>|?>>
    <associate|LC313|<tuple|6.5|?>>
    <associate|LC98|<tuple|6.2.2|?>>
    <associate|auto-1|<tuple|1|5>>
    <associate|auto-10|<tuple|2.2.1|8>>
    <associate|auto-11|<tuple|2.2.2|8>>
    <associate|auto-12|<tuple|2.2.3|8>>
    <associate|auto-13|<tuple|2.2.4|9>>
    <associate|auto-14|<tuple|2.2.5|9>>
    <associate|auto-15|<tuple|2.2.6|9>>
    <associate|auto-16|<tuple|2.2.7|9>>
    <associate|auto-17|<tuple|2.2.8|9>>
    <associate|auto-18|<tuple|2.2.9|9>>
    <associate|auto-19|<tuple|2.2.10|10>>
    <associate|auto-2|<tuple|1.1|5>>
    <associate|auto-20|<tuple|2.2.11|10>>
    <associate|auto-21|<tuple|2.3|10>>
    <associate|auto-22|<tuple|2.3.1|10>>
    <associate|auto-23|<tuple|2.3.2|11>>
    <associate|auto-24|<tuple|2.3.3|15>>
    <associate|auto-25|<tuple|2.3.4|15>>
    <associate|auto-26|<tuple|2.3.5|15>>
    <associate|auto-27|<tuple|2.3.6|15>>
    <associate|auto-28|<tuple|2.4|15>>
    <associate|auto-29|<tuple|2.5|16>>
    <associate|auto-3|<tuple|2|7>>
    <associate|auto-30|<tuple|2.5.1|16>>
    <associate|auto-31|<tuple|2.5.2|16>>
    <associate|auto-32|<tuple|2.1|17>>
    <associate|auto-33|<tuple|2.5.2.1|17>>
    <associate|auto-34|<tuple|2.5.2.2|17>>
    <associate|auto-35|<tuple|2.5.2.3|18>>
    <associate|auto-36|<tuple|2.5.2.4|18>>
    <associate|auto-37|<tuple|2.5.2.5|18>>
    <associate|auto-38|<tuple|2.5.3|19>>
    <associate|auto-39|<tuple|2.5.3.1|19>>
    <associate|auto-4|<tuple|2.1|7>>
    <associate|auto-40|<tuple|2.6|21>>
    <associate|auto-41|<tuple|2.6.1|21>>
    <associate|auto-42|<tuple|2.6.1.1|21>>
    <associate|auto-43|<tuple|2.6.1.2|21>>
    <associate|auto-44|<tuple|2.6.2|21>>
    <associate|auto-45|<tuple|2.6.3|21>>
    <associate|auto-46|<tuple|2.7|23>>
    <associate|auto-47|<tuple|2.7.1|23>>
    <associate|auto-48|<tuple|3|23>>
    <associate|auto-49|<tuple|3.1|23>>
    <associate|auto-5|<tuple|2.1.1|7>>
    <associate|auto-50|<tuple|3.1.1|23>>
    <associate|auto-51|<tuple|3.2|23>>
    <associate|auto-52|<tuple|3.3|23>>
    <associate|auto-53|<tuple|3.3.1|23>>
    <associate|auto-54|<tuple|3.3.2|23>>
    <associate|auto-55|<tuple|3.3.3|23>>
    <associate|auto-56|<tuple|3.4|23>>
    <associate|auto-57|<tuple|3.4.1|23>>
    <associate|auto-58|<tuple|3.4.2|23>>
    <associate|auto-59|<tuple|3.5|25>>
    <associate|auto-6|<tuple|2.1.1.1|7>>
    <associate|auto-60|<tuple|3.5.1|25>>
    <associate|auto-61|<tuple|4|27>>
    <associate|auto-62|<tuple|4.1|27>>
    <associate|auto-63|<tuple|5|29>>
    <associate|auto-64|<tuple|5.1|29>>
    <associate|auto-65|<tuple|6|29>>
    <associate|auto-66|<tuple|6.1|29>>
    <associate|auto-67|<tuple|6.2|29>>
    <associate|auto-68|<tuple|6.2.1|30>>
    <associate|auto-69|<tuple|6.2.2|30>>
    <associate|auto-7|<tuple|2.1.2|7>>
    <associate|auto-70|<tuple|6.2.2.1|31>>
    <associate|auto-71|<tuple|6.2.2.2|31>>
    <associate|auto-72|<tuple|6.2.2.3|31>>
    <associate|auto-73|<tuple|6.2.3|31>>
    <associate|auto-74|<tuple|6.3|31>>
    <associate|auto-75|<tuple|6.3.1|32>>
    <associate|auto-76|<tuple|6.3.2|33>>
    <associate|auto-77|<tuple|6.4|33>>
    <associate|auto-78|<tuple|6.4.1|34>>
    <associate|auto-79|<tuple|6.4.1.1|35>>
    <associate|auto-8|<tuple|2.1.2.1|8>>
    <associate|auto-80|<tuple|6.4.2|35>>
    <associate|auto-81|<tuple|6.4.3|36>>
    <associate|auto-82|<tuple|7|36>>
    <associate|auto-83|<tuple|7.1|36>>
    <associate|auto-84|<tuple|7.2|36>>
    <associate|auto-85|<tuple|7.3|37>>
    <associate|auto-86|<tuple|7.3.1|37>>
    <associate|auto-87|<tuple|7.3.2|37>>
    <associate|auto-88|<tuple|7.3.2.1|37>>
    <associate|auto-89|<tuple|7.3.2.2|37>>
    <associate|auto-9|<tuple|2.2|8>>
    <associate|auto-90|<tuple|7.3.3|38>>
    <associate|auto-91|<tuple|7.3.4|38>>
    <associate|auto-92|<tuple|7.4|39>>
    <associate|auto-93|<tuple|7.4.1|?>>
    <associate|auto-94|<tuple|7.4.2|?>>
    <associate|auto-95|<tuple|8|?>>
    <associate|auto-96|<tuple|8|?>>
    <associate|footnote-1|<tuple|1|?>>
    <associate|footnote-2.1|<tuple|2.1|17>>
    <associate|footnr-2.1|<tuple|2.1|17>>
    <associate|full-adder-LHS|<tuple|2.3|14>>
    <associate|full-adder-RHS|<tuple|2.2|14>>
    <associate|full-adder-spec|<tuple|2.1|13>>
    <associate|thm:CSCT|<tuple|2.2|15>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|figure>
      <tuple|normal|Example state of the Bit Machine.|<pageref|auto-32>>
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

      <with|par-left|<quote|2tab>|2.5.2.1<space|2spc>Frame operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|2tab>|2.5.2.2<space|2spc>Active Write Frame
      operations <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|2tab>|2.5.2.3<space|2spc>Active Read Frame
      operations <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <with|par-left|<quote|2tab>|2.5.2.4<space|2spc>Crashing the Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36>>

      <with|par-left|<quote|2tab>|2.5.2.5<space|2spc>Bit Machine programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>>

      <with|par-left|<quote|1tab>|2.5.3<space|2spc>Executing Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38>>

      <with|par-left|<quote|2tab>|2.5.3.1<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>>

      2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>

      <with|par-left|<quote|1tab>|2.6.1<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>>

      <with|par-left|<quote|2tab>|2.6.1.1<space|2spc>Maximum Cell Count Bound
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>>

      <with|par-left|<quote|2tab>|2.6.1.2<space|2spc>Maximum Frame Count
      Bound <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>>

      <with|par-left|<quote|1tab>|2.6.2<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>>

      <with|par-left|<quote|1tab>|2.6.3<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45>>

      2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>

      <with|par-left|<quote|1tab>|2.7.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Full
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48><vspace|0.5fn>

      3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>

      <with|par-left|<quote|1tab>|3.1.1<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>>

      3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>

      3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52>

      <with|par-left|<quote|1tab>|3.3.1<space|2spc>Hidden Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53>>

      <with|par-left|<quote|1tab>|3.3.2<space|2spc>Serialization with Oracles
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54>>

      <with|par-left|<quote|1tab>|3.3.3<space|2spc>Type Inference with
      Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55>>

      3.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56>

      <with|par-left|<quote|1tab>|3.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57>>

      <with|par-left|<quote|1tab>|3.4.2<space|2spc>Schnorr Signature
      Aggregation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58>>

      3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-59>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-60>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Jetted
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-61><vspace|0.5fn>

      4.1<space|2spc>Example: The Standard Single Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-62>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Extended
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-63><vspace|0.5fn>

      5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-64>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-65><vspace|0.5fn>

      6.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-66>

      6.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-67>

      <with|par-left|<quote|1tab>|6.2.1<space|2spc>The ``Initial''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-68>>

      <with|par-left|<quote|1tab>|6.2.2<space|2spc>The ``Final''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-69>>

      <with|par-left|<quote|2tab>|6.2.2.1<space|2spc>Simplicity Algebras
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-70>>

      <with|par-left|<quote|2tab>|6.2.2.2<space|2spc>The ``Final''
      Representation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-71>>

      <with|par-left|<quote|2tab>|6.2.2.3<space|2spc>Constructing ``Final''
      Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-72>>

      <with|par-left|<quote|1tab>|6.2.3<space|2spc>Why two representations of
      Terms? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-73>>

      6.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-74>

      <with|par-left|<quote|1tab>|6.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-75>>

      <with|par-left|<quote|1tab>|6.3.2<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-76>>

      6.4<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-77>

      <with|par-left|<quote|1tab>|6.4.1<space|2spc>Bit Machine Code
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-78>>

      <with|par-left|<quote|2tab>|6.4.1.1<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-79>>

      <with|par-left|<quote|1tab>|6.4.2<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-80>>

      <with|par-left|<quote|1tab>|6.4.3<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-81>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-82><vspace|0.5fn>

      7.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-83>

      7.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-84>

      7.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-85>

      <with|par-left|<quote|1tab>|7.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-86>>

      <with|par-left|<quote|1tab>|7.3.2<space|2spc>Multi-bit Words
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-87>>

      <with|par-left|<quote|2tab>|7.3.2.1<space|2spc>Arithmetic operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-88>>

      <with|par-left|<quote|2tab>|7.3.2.2<space|2spc>Bit-wise operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-89>>

      <with|par-left|<quote|1tab>|7.3.3<space|2spc>Generic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-90>>

      <with|par-left|<quote|1tab>|7.3.4<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-91>>

      7.4<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-92>

      <with|par-left|<quote|1tab>|7.4.1<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-93>>

      <with|par-left|<quote|1tab>|7.4.2<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-94>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-95><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>
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

    <with|par-left|1tab|2.5.1<space|2spc>Repesenting Values as Bit Strings
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|1tab|2.5.2<space|2spc>Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    <with|par-left|1tab|2.5.3<space|2spc>Tail Composition Optimisation (TCO)
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-32>>

    2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>

    <with|par-left|1tab|2.6.1<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <with|par-left|1tab|2.6.2<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    <with|par-left|1tab|2.6.3<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-36>>

    2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>

    <with|par-left|1tab|2.7.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-38>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Full
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39><vspace|0.5fn>

    3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-40>

    <with|par-left|1tab|3.1.1<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-41>>

    3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-42>

    3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-43>

    <with|par-left|1tab|3.3.1<space|2spc>Hidden Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>>

    <with|par-left|1tab|3.3.2<space|2spc>Serialization with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-45>>

    <with|par-left|1tab|3.3.3<space|2spc>Type Inference with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46>>

    3.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>

    <with|par-left|1tab|3.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    <with|par-left|1tab|3.4.2<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49>>

    3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>

    <with|par-left|1tab|3.5.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Jetted
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52><vspace|0.5fn>

    4.1<space|2spc>Example: The Standard Single Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Extended
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54><vspace|0.5fn>

    5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58><vspace|0.5fn>
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

  <assign|1|\<b-1\>>Simplicity operates over three kinds of types:

  <\itemize-minus>
    <item>The unit type, written as <math|<value|1>>.

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

  <assign|2|<math|\<b-2\>>>Let us define a type of two values for Booleans,
  or Bit. \ We will denote this type by <math|<2>>.

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
    s t>>|<row|<cell|s;t>|<cell|\<assign\>>|<cell|<math-ss|cut> s t>>>>
  </eqnarray*>

  with the <math|\<times\>> operator having higher precidence than the
  <math|;> operator.

  Composition of sequences of \ <samp|drop> and <samp|take> with <samp|ident>
  is a very common way of picking data out of nested tuples of input. \ To
  make this more concise we will use the following notation.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|H>>|<cell|\<assign\>>|<cell|<math-ss|ident>>>|<row|<cell|<math-ss|O>s<math-ss|>>|<cell|\<assign\>>|<cell|<math-ss|take>
    s>>|<row|<cell|<math-ss|I>s<math-ss|>*>|<cell|\<assign\>>|<cell|<math-ss|drop>
    s>>>>
  </eqnarray*>

  where <math|s> is a string of <samp|I>'s and <samp|O>'s that ends with
  <samp|H>.

  For completely formal definitions please refer to the Coq library.

  By repeatedly taking products of bit types we can build types for
  <math|2<rsup|n>> bit words of any size we want.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-bf|Word2>>|<cell|\<assign\>>|<cell|<2>\<times\><2>>>|<row|<cell|<math-bf|Word4>>|<cell|\<assign\>>|<cell|<math-bf|Word2>
    \<times\><math-bf|Word2>>>|<row|<cell|<math-bf|Word8>>|<cell|\<assign\>>|<cell|<math-bf|Word4>
    \<times\><math-bf|Word4>>>|<row|<cell|<math-bf|Word16>>|<cell|\<assign\>>|<cell|<math-bf|Word8>
    \<times\><math-bf|Word8>>>|<row|<cell|<math-bf|Word32>>|<cell|\<assign\>>|<cell|<math-bf|Word16>
    \<times\><math-bf|Word16>>>|<row|<cell|<math-bf|Word64>>|<cell|\<assign\>>|<cell|<math-bf|Word32>
    \<times\><math-bf|Word32>>>|<row|<cell|<math-bf|Word128>>|<cell|\<assign\>>|<cell|<math-bf|Word64>
    \<times\><math-bf|Word64>>>|<row|<cell|<math-bf|Word256>>|<cell|\<assign\>>|<cell|<math-bf|Word128>
    \<times\><math-bf|Word128>>>>>
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
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|0<rsub|<2>>|\<rfloor\>><rsub|1>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\<lfloor\>|1<rsub|<2>>|\<rfloor\>><rsub|1>>|<cell|\<assign\>>|<cell|1>>|<row|<cell|<around*|\<lfloor\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rfloor\>><rsub|2n>>|<cell|\<assign\>>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|n>>>>>
  </eqnarray*>

  We will also make use of the following variation of this value conversion
  function.

  <\equation*>
    <around*|\<lfloor\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rfloor\>><rsub|n,m>\<assign\><around*|\<lfloor\>|a|\<rfloor\>><rsub|n>\<cdot\>2<rsup|m>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|m>
  </equation*>

  These value conversion functions are all injective (one-to-one).

  Using techniques familiar from digitial logic we can build an adders and
  full adders from our Boolean operations defined in the previous section.
  \ We begin with definitions of the single bit adder and full adder.

  <\render-code>
    <math|<math-ss|adder><rsub|1> :<2>\<times\><2>\<vdash\><2>\<times\><math-bf|<2>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|cond>
    <around*|(|<math-ss|iden>\<times\><math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false>\<times\><math-ss|iden>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-adder><rsub|1> :<around*|(|<2>\<times\><2>|)>\<times\><2>\<vdash\><2>\<times\><math-bf|<2>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <math-ss|adder><rsub|1>\<times\> <math-ss|IH>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|OOH>\<times\><around*|(|<math-ss|OIH>\<times\>
    <math-ss|IH> ;<math-ss|adder><rsub|1>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|<math|<math-ss|cond>
    <math-ss|true> <math-ss|OH>\<times\><math-ss|IIH>>>>>>>>>>>>>>
  </render-code>

  We can prove that these two adders meet the following specification.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rfloor\>><rsub|2>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|1>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|1>>>|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rfloor\>><rsub|2>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|1>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|1>+<around*|\<lfloor\>|c|\<rfloor\>><rsub|1>>>>>
  </eqnarray*>

  Next we recursively build adders and full adders for any word size.

  <\render-code>
    <math|<math-ss|full-adder><rsub|2n> :<around*|(|<math-bf|Word2<em|n>>\<times\><math-bf|Word2<em|n>>|)>\<times\><2>\<vdash\><2>\<times\><math-bf|Word2<em|n>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|2n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>\<times\><around*|(|<math-ss|take>
    <around*|(|<math-ss|OIH>\<times\><math-ss|IIH>|)>\<times\> <math-ss|IH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|adder><rsub|2n> :<math-bf|Word2<em|n>>\<times\><math-bf|Word2<em|n>>\<vdash\><2>\<times\><math-bf|Word2<em|n>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|2n>>>|<cell|:=>|<cell|<math|<around*|(|<math-ss|OOH>\<times\><math-ss|IOH>|)>\<times\><around*|(|<math-ss|OIH>\<times\><math-ss|IIH>
    ;<math-ss|adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>\<times\><around*|(|<math-ss|OH>\<times\><math-ss|IOH>
    ;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>\<times\><around*|(|<math-ss|IIH>\<times\><math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  We generalize the specification for the single bit adders and full adders
  to the multi-bit adders and full adders.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rfloor\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|n>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|n>>>|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rfloor\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|n>+<around*|\<lfloor\>|b|\<rfloor\>><rsub|n>+<around*|\<lfloor\>|c|\<rfloor\>><rsub|1>>>>>
  </eqnarray*>

  With a full adder we can recursively build multipliers and full multiplier
  in a similar way.

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|1>
    :<around*|(|<2>\<times\><2>|)>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><math|<math-bf|Word2>>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|IH>\<times\><math-ss|take>
    <around*|(|<math-ss|cond> <math-ss|iden> <math-ss|false>|)>
    ;<math-ss|full-adder><rsub|1>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|2n>
    :<around*|(|<math-bf|Word2<em|n>>\<times\><math-bf|Word2<em|n>>|)>\<times\><around*|(|<math-bf|Word2<em|n>>\<times\><math-bf|Word2<em|n>>|)>\<vdash\><math|<math-bf|Word4<em|n>>>>

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
    <math|<math-ss|multiplier><rsub|1> :<2>\<times\><2>\<vdash\>><math|<math-bf|Word2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|false>\<times\><math-ss|cond>
    <math-ss|iden> ><samp|false>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|multiplier><rsub|2n> :<math-bf|Word2<em|n>>\<times\><math-bf|Word2<em|n>>\<vdash\><math|<math-bf|Word4<em|n>>>>

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
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|full-multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,<around*|\<langle\>|c,d|\<rangle\>>|\<rangle\>>|\<rfloor\>><rsub|2*n>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|n>\<cdot\><around*|\<lfloor\>|b|\<rfloor\>><rsub|n>+<around*|\<lfloor\>|c|\<rfloor\>><rsub|n>+<around*|\<lfloor\>|d|\<rfloor\>><rsub|n>>>|<row|<cell|<around*|\<lfloor\>|<around*|\<llbracket\>|<math-ss|multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rfloor\>><rsub|2n>>|<cell|=>|<cell|<around*|\<lfloor\>|a|\<rfloor\>><rsub|n>\<cdot\><around*|\<lfloor\>|b|\<rfloor\>><rsub|n>>>>>
  </eqnarray*>

  \;

  <with|color|red|TODO: notes on tradeoffs between efficency and simplicity.>

  <subsection|Bitwise Operations>

  <subsection|SHA-256>

  <subsection|Modular Arithmetic>

  <subsection|Elliptic Curve Operations>

  <section|Completeness Theorem>

  <section|Operational Semantics>

  <subsection|Repesenting Values as Bit Strings>

  <subsection|Bit Machine>

  <subsection|Tail Composition Optimisation (TCO)>

  <section|Static Analysis>

  <subsection|Commitment Merkle Root>

  <subsection|Space Resources>

  <subsection|Time Resources>

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

  <chapter|Haskell Library Guide>

  <chapter|C Library Guide>
</body>

<\initial>
  <\collection>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|5>>
    <associate|auto-10|<tuple|2.2.1|8>>
    <associate|auto-11|<tuple|2.2.2|8>>
    <associate|auto-12|<tuple|2.2.3|8>>
    <associate|auto-13|<tuple|2.2.4|8>>
    <associate|auto-14|<tuple|2.2.5|9>>
    <associate|auto-15|<tuple|2.2.6|9>>
    <associate|auto-16|<tuple|2.2.7|9>>
    <associate|auto-17|<tuple|2.2.8|9>>
    <associate|auto-18|<tuple|2.2.9|9>>
    <associate|auto-19|<tuple|2.2.10|9>>
    <associate|auto-2|<tuple|1.1|5>>
    <associate|auto-20|<tuple|2.2.11|10>>
    <associate|auto-21|<tuple|2.3|10>>
    <associate|auto-22|<tuple|2.3.1|10>>
    <associate|auto-23|<tuple|2.3.2|11>>
    <associate|auto-24|<tuple|2.3.3|13>>
    <associate|auto-25|<tuple|2.3.4|13>>
    <associate|auto-26|<tuple|2.3.5|13>>
    <associate|auto-27|<tuple|2.3.6|13>>
    <associate|auto-28|<tuple|2.4|13>>
    <associate|auto-29|<tuple|2.5|13>>
    <associate|auto-3|<tuple|2|7>>
    <associate|auto-30|<tuple|2.5.1|13>>
    <associate|auto-31|<tuple|2.5.2|13>>
    <associate|auto-32|<tuple|2.5.3|13>>
    <associate|auto-33|<tuple|2.6|13>>
    <associate|auto-34|<tuple|2.6.1|13>>
    <associate|auto-35|<tuple|2.6.2|13>>
    <associate|auto-36|<tuple|2.6.3|13>>
    <associate|auto-37|<tuple|2.7|13>>
    <associate|auto-38|<tuple|2.7.1|13>>
    <associate|auto-39|<tuple|3|15>>
    <associate|auto-4|<tuple|2.1|7>>
    <associate|auto-40|<tuple|3.1|15>>
    <associate|auto-41|<tuple|3.1.1|15>>
    <associate|auto-42|<tuple|3.2|15>>
    <associate|auto-43|<tuple|3.3|15>>
    <associate|auto-44|<tuple|3.3.1|15>>
    <associate|auto-45|<tuple|3.3.2|15>>
    <associate|auto-46|<tuple|3.3.3|15>>
    <associate|auto-47|<tuple|3.4|15>>
    <associate|auto-48|<tuple|3.4.1|15>>
    <associate|auto-49|<tuple|3.4.2|15>>
    <associate|auto-5|<tuple|2.1.1|7>>
    <associate|auto-50|<tuple|3.5|15>>
    <associate|auto-51|<tuple|3.5.1|15>>
    <associate|auto-52|<tuple|4|17>>
    <associate|auto-53|<tuple|4.1|17>>
    <associate|auto-54|<tuple|5|19>>
    <associate|auto-55|<tuple|5.1|19>>
    <associate|auto-56|<tuple|6|21>>
    <associate|auto-57|<tuple|7|23>>
    <associate|auto-58|<tuple|8|25>>
    <associate|auto-59|<tuple|8|?>>
    <associate|auto-6|<tuple|2.1.1.1|7>>
    <associate|auto-7|<tuple|2.1.2|7>>
    <associate|auto-8|<tuple|2.1.2.1|8>>
    <associate|auto-9|<tuple|2.2|8>>
  </collection>
</references>

<\auxiliary>
  <\collection>
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

      <with|par-left|<quote|1tab>|2.5.1<space|2spc>Repesenting Values as Bit
      Strings <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|2.5.2<space|2spc>Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <with|par-left|<quote|1tab>|2.5.3<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32>>

      2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>

      <with|par-left|<quote|1tab>|2.6.1<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|1tab>|2.6.2<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <with|par-left|<quote|1tab>|2.6.3<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36>>

      2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>

      <with|par-left|<quote|1tab>|2.7.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Full
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39><vspace|0.5fn>

      3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>

      <with|par-left|<quote|1tab>|3.1.1<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>>

      3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>

      3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>

      <with|par-left|<quote|1tab>|3.3.1<space|2spc>Hidden Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>>

      <with|par-left|<quote|1tab>|3.3.2<space|2spc>Serialization with Oracles
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45>>

      <with|par-left|<quote|1tab>|3.3.3<space|2spc>Type Inference with
      Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>>

      3.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>

      <with|par-left|<quote|1tab>|3.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      <with|par-left|<quote|1tab>|3.4.2<space|2spc>Schnorr Signature
      Aggregation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>>

      3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Jetted
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52><vspace|0.5fn>

      4.1<space|2spc>Example: The Standard Single Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Extended
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54><vspace|0.5fn>

      5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>
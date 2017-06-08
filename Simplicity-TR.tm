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

    <with|par-left|1tab|2.3.5<space|2spc>Elliptic Curve Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26>>

    2.4<space|2spc>Completeness Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27>

    2.5<space|2spc>Operational Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28>

    <with|par-left|1tab|2.5.1<space|2spc>Repesenting Values as Bit Strings
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-29>>

    <with|par-left|1tab|2.5.2<space|2spc>Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|1tab|2.5.3<space|2spc>Tail Composition Optimisation (TCO)
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-32>

    <with|par-left|1tab|2.6.1<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>>

    <with|par-left|1tab|2.6.2<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <with|par-left|1tab|2.6.3<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-36>

    <with|par-left|1tab|2.7.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Full
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-38><vspace|0.5fn>

    3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39>

    <with|par-left|1tab|3.1.1<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-40>>

    3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-41>

    3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-42>

    <with|par-left|1tab|3.3.1<space|2spc>Hidden Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-43>>

    <with|par-left|1tab|3.3.2<space|2spc>Serialization with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>>

    <with|par-left|1tab|3.3.3<space|2spc>Type Inference with Oracles
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-45>>

    3.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46>

    <with|par-left|1tab|3.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>>

    <with|par-left|1tab|3.4.2<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49>

    <with|par-left|1tab|3.5.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Jetted
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51><vspace|0.5fn>

    4.1<space|2spc>Example: The Standard Single Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Extended
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53><vspace|0.5fn>

    5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57><vspace|0.5fn>
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
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|iden<rsub|A>
    : A\<vdash\>A>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|iden|\<rrbracket\>><around*|(|a|)>=a
  </equation*>

  For every type <math|A> there we have an identity term that denotes the
  identity function for that type.\ 

  Like the type annotations on values, the type argument for <math|iden>
  usually can be infered and therefore we will usually omit (as we did for
  the denotation equation above). \ Similarly, we will usually omit the type
  arguments for all the other Simplicity combinators.

  <subsection|Composition>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : B\<vdash\>C>>>|<row|<cell|<math|comp<rsub|A,B,C> s t:
    A\<vdash\>C>>|<cell|>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|comp s t|\<rrbracket\>><around*|(|a|)>=<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>|)>
  </equation*>

  The composition combinator functionally composes its two arguments,
  <math|s> and <math|t>, when the output type of <math|s> matches the input
  type of <math|t>.

  <subsection|Constant Unit>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|unit<rsub|A>
    : A\<vdash\><value|1>>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|unit|\<rrbracket\>><around*|(|a|)>=<around*|\<langle\>||\<rangle\>>
  </equation*>

  The constant unit term ignores its argument and always returns
  <math|<around*|\<langle\>||\<rangle\>>>, the unique value of the unit type.
  Since the argument is ignored, we have a constant unit term for every type.

  <subsection|Left Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>B>>>|<row|<cell|<math|injl<rsub|A,B,C>
    t: A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|injl t|\<rrbracket\>><around*|(|a|)>=<injl|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The left injection combinator composes a left-tag with its argument
  <math|t>.

  <subsection|Right Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>C>>>|<row|<cell|<math|injr<rsub|A,B,C>
    t: A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|injr t|\<rrbracket\>><around*|(|a|)>=<injr|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The right injection combinator composes a right-tag with its argument
  <math|t>.

  <subsection|Case>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|s:A\<times\>C\<vdash\>D>>|<cell|<math|t
    : B\<times\>C\<vdash\>D>>>|<row|<cell|<math|case<rsub|A,B,C,D> s t:
    <around*|(|A+B|)>\<times\>C\<vdash\>D>>|<cell|>>>>>
  </with>

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|case s
    t|\<rrbracket\>><around*|\<langle\>|<injl|<around*|(|a|)>,c>|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|case
    s t|\<rrbracket\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|\<langle\>|b,c|\<rangle\>>>>>>
  </eqnarray*>

  The case combinator is Simplicity's only branching operation. \ Given a
  pair of values with the first component being a sum type, this combinator
  evalutes either its <math|s> or <math|t> argument depending on which tag
  the first component has, on the pair of inputs.

  <subsection|Pair>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|s:A\<vdash\>B>>|<cell|<math|t
    : A\<vdash\>C>>>|<row|<cell|<math|pair<rsub|A,B,C> s t:
    A\<vdash\>B\<times\>C>>|<cell|>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|pair s t|\<rrbracket\>><around*|(|a|)>=<around*|\<langle\>|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>,<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|\<rangle\>>
  </equation*>

  The pair combinator executes both its arguments, <math|s> and <math|t>, on
  the same input and returns the pair of the two results.

  <subsection|Take>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:A\<vdash\>C>>>|<row|<cell|<math|take<rsub|A,B,C>
    t: A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|take t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>=<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>
  </equation*>

  The take combinator denotes a function on pairs that passes its first
  component to <math|t> and ignores its second component.

  <subsection|Drop>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t:B\<vdash\>C>>>|<row|<cell|<math|drop<rsub|A,B,C>
    t: A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|drop t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>=<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|b|)>
  </equation*>

  The drop combinator denotes a function on pairs that passes its second
  component to <math|t> and ignores its first component.

  <subsection|Formal Syntax>

  We define the formal syntax of well-typed core Simplicity terms as an
  inductive family in Coq:

  <\render-code>
    <\verbatim>
      <strong|Inductive> Term : Ty -\<gtr\> Ty -\<gtr\> Set :=

      \| iden : forall {A : Ty}, Term A A

      \| comp : forall {A B C : Ty}, Term A B -\<gtr\> Term B C -\<gtr\> Term
      A C

      \| unit : forall {A : Ty}, Term A Unit

      \| injl : forall {A B C : Ty}, Term A B -\<gtr\> Term A (Sum B C)

      \| injr : forall {A B C : Ty}, Term A C -\<gtr\> Term A (Sum B C)

      \| case : forall {A B C D : Ty},

      \ \ \ \ Term (Prod A C) D -\<gtr\> Term (Prod B C) D -\<gtr\> Term
      (Prod (Sum A B) C) D

      \| pair : forall {A B C : Ty}, Term A B -\<gtr\> Term A C -\<gtr\> Term
      A (Prod B C)

      \| take : forall {A B C : Ty}, Term A C -\<gtr\> Term (Prod A B) C

      \| drop : forall {A B C : Ty}, Term B C -\<gtr\> Term (Prod A B) C.
    </verbatim>
  </render-code>

  <subsection|Formal Semantics>

  \;

  <\verbatim>
    Fixpoint eval {A B : Ty} (x : Term A B) : tySem A -\<gtr\> tySem B :=

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

  <subsection|Bit Operations>

  <subsection|Arithmetic>

  <subsection|Bitwise Operations>

  <subsection|SHA-256>

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
    <associate|auto-14|<tuple|2.2.5|8>>
    <associate|auto-15|<tuple|2.2.6|8>>
    <associate|auto-16|<tuple|2.2.7|8>>
    <associate|auto-17|<tuple|2.2.8|8>>
    <associate|auto-18|<tuple|2.2.9|8>>
    <associate|auto-19|<tuple|2.2.10|8>>
    <associate|auto-2|<tuple|1.1|5>>
    <associate|auto-20|<tuple|2.2.11|9>>
    <associate|auto-21|<tuple|2.3|9>>
    <associate|auto-22|<tuple|2.3.1|9>>
    <associate|auto-23|<tuple|2.3.2|9>>
    <associate|auto-24|<tuple|2.3.3|9>>
    <associate|auto-25|<tuple|2.3.4|9>>
    <associate|auto-26|<tuple|2.3.5|9>>
    <associate|auto-27|<tuple|2.4|9>>
    <associate|auto-28|<tuple|2.5|9>>
    <associate|auto-29|<tuple|2.5.1|9>>
    <associate|auto-3|<tuple|2|7>>
    <associate|auto-30|<tuple|2.5.2|9>>
    <associate|auto-31|<tuple|2.5.3|9>>
    <associate|auto-32|<tuple|2.6|9>>
    <associate|auto-33|<tuple|2.6.1|9>>
    <associate|auto-34|<tuple|2.6.2|9>>
    <associate|auto-35|<tuple|2.6.3|9>>
    <associate|auto-36|<tuple|2.7|9>>
    <associate|auto-37|<tuple|2.7.1|9>>
    <associate|auto-38|<tuple|3|11>>
    <associate|auto-39|<tuple|3.1|11>>
    <associate|auto-4|<tuple|2.1|7>>
    <associate|auto-40|<tuple|3.1.1|11>>
    <associate|auto-41|<tuple|3.2|11>>
    <associate|auto-42|<tuple|3.3|11>>
    <associate|auto-43|<tuple|3.3.1|11>>
    <associate|auto-44|<tuple|3.3.2|11>>
    <associate|auto-45|<tuple|3.3.3|11>>
    <associate|auto-46|<tuple|3.4|11>>
    <associate|auto-47|<tuple|3.4.1|11>>
    <associate|auto-48|<tuple|3.4.2|11>>
    <associate|auto-49|<tuple|3.5|11>>
    <associate|auto-5|<tuple|2.1.1|7>>
    <associate|auto-50|<tuple|3.5.1|11>>
    <associate|auto-51|<tuple|4|13>>
    <associate|auto-52|<tuple|4.1|13>>
    <associate|auto-53|<tuple|5|15>>
    <associate|auto-54|<tuple|5.1|15>>
    <associate|auto-55|<tuple|6|17>>
    <associate|auto-56|<tuple|7|19>>
    <associate|auto-57|<tuple|8|21>>
    <associate|auto-6|<tuple|2.1.1.1|7>>
    <associate|auto-7|<tuple|2.1.2|7>>
    <associate|auto-8|<tuple|2.1.2.1|7>>
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

      <with|par-left|<quote|1tab>|2.3.5<space|2spc>Elliptic Curve Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      2.4<space|2spc>Completeness Theorem
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27>

      2.5<space|2spc>Operational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28>

      <with|par-left|<quote|1tab>|2.5.1<space|2spc>Repesenting Values as Bit
      Strings <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>>

      <with|par-left|<quote|1tab>|2.5.2<space|2spc>Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|2.5.3<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      2.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32>

      <with|par-left|<quote|1tab>|2.6.1<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|1tab>|2.6.2<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|1tab>|2.6.3<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      2.7<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36>

      <with|par-left|<quote|1tab>|2.7.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Full
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38><vspace|0.5fn>

      3.1<space|2spc>Assertions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>

      <with|par-left|<quote|1tab>|3.1.1<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>>

      3.2<space|2spc>Witness Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>

      3.3<space|2spc>Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>

      <with|par-left|<quote|1tab>|3.3.1<space|2spc>Hidden Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>>

      <with|par-left|<quote|1tab>|3.3.2<space|2spc>Serialization with Oracles
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>>

      <with|par-left|<quote|1tab>|3.3.3<space|2spc>Type Inference with
      Oracles <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45>>

      3.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>

      <with|par-left|<quote|1tab>|3.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>>

      <with|par-left|<quote|1tab>|3.4.2<space|2spc>Schnorr Signature
      Aggregation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      3.5<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Jetted
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51><vspace|0.5fn>

      4.1<space|2spc>Example: The Standard Single Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Extended
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53><vspace|0.5fn>

      5.1<space|2spc>Disconnect <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>
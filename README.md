[![pipeline status](https://gitlab.com/math-comp/math-comp/badges/master/pipeline.svg)](https://gitlab.com/math-comp/math-comp/commits/master)
[![Join the chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237664-math-comp-users)

# The Mathematical Components repository

The Mathematical Components Library is an extensive and coherent
repository of formalized mathematical theories. It is based on
the [Coq](http://coq.inria.fr) proof assistant, powered with the
[Coq/SSReflect](https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html)
language.

These formal theories cover a wide spectrum of topics, ranging from the formal theory of general purpose data structures like [lists](mathcomp/ssreflect/seq.v), [prime numbers](mathcomp/ssreflect/prime.v) or [finite graphs](mathcomp/ssreflect/fingraph.v), to advanced topics in algebra. The repository includes the foundation of formal theories used in a [formal proof](https://www.ams.org/notices/200811/tx081101382p.pdf) of the [Four Colour Theorem](https://en.wikipedia.org/wiki/Four_color_theorem) (Appel - Haken, 1976) and a [mechanization](https://hal.archives-ouvertes.fr/hal-00816699/) of the [Odd Order Theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem) (Feit - Thompson, 1963), a landmark result of finite group theory, which utilizes the library extensively.

## Installation

If you already have OPAM installed (a fresh or up to date version of opam 2 is required):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

Additional packages go by the name of `coq-mathcomp-algebra`,
`coq-mathcomp-field`, etc... See [INSTALL](INSTALL.md) for detailed
installation instructions in other scenarios.

## How to get help

- The [website](http://math-comp.github.io/math-comp/) of the MathComp library
  contains:
  + links to the [HTML documentation of the last version](https://math-comp.github.io/htmldoc/libgraph.html) as well as the documentation of previous versions,
  + a list of [tutorials](https://math-comp.github.io/documentation.html)
- The [ssreflect mailing list](https://sympa.inria.fr/sympa/info/ssreflect) is the primary
  venue for help and questions about the library.
- The [Mathematical Components Book](https://math-comp.github.io/mcb/)
  provides a comprehensive introduction to the library.
- Experienced users hang around at
  [StackOverflow](https://stackoverflow.com/questions/tagged/ssreflect)
  listening to the `ssreflect` and `coq` tags.

## Publications and Tools using MathComp

[A collection of papers using the Mathematical Components library](https://math-comp.github.io/papers.html)

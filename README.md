# ![Catlab.jl](docs/src/assets/logo.png) Catlab.jl
<!-- ALL-CONTRIBUTORS-BADGE:START - Do not remove or modify this section -->
[![All Contributors](https://img.shields.io/badge/all_contributors-1-orange.svg?style=flat-square)](#contributors-)
<!-- ALL-CONTRIBUTORS-BADGE:END -->

[![Build Status](https://github.com/AlgebraicJulia/Catlab.jl/workflows/Tests/badge.svg)](https://github.com/AlgebraicJulia/Catlab.jl/actions?query=workflow%3ATests)
[![Stable Docs](https://img.shields.io/badge/docs-stable-blue.svg)](https://algebraicjulia.github.io/Catlab.jl/stable)
[![Dev Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://algebraicjulia.github.io/Catlab.jl/dev)
[![Code Coverage](https://codecov.io/gh/AlgebraicJulia/Catlab.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/AlgebraicJulia/Catlab.jl)
[![DOI](https://img.shields.io/badge/DOI-10.17605%2FOSF.IO%2FHMNFE-blue)](https://doi.org/10.17605/OSF.IO/HMNFE)

Catlab.jl is a framework for applied and computational category theory, written
in the [Julia](https://julialang.org) language. Catlab provides a programming
library and interactive interface for applications of category theory to
scientific and engineering fields. It emphasizes monoidal categories due to
their wide applicability but can support any categorical structure that is
formalizable as a generalized algebraic theory.

## Getting started

The [documentation](https://algebraicjulia.github.io/Catlab.jl/latest) contains
several example notebooks, as well as partial API docs. However, we readily
acknowledge that the documentation is not as well developed as it should be.
Feel free to ask questions! Besides the GitHub issues, we have a
[#catlab.jl](https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl)
stream on the [Julia Zulip](https://julialang.zulipchat.com/) (preferred) and
also a [#catlab](https://julialang.slack.com/archives/CQNUDDF5L) channel on the
[Julia Slack](https://julialang.org/slack/) (less preferred).

### Contributing

Catlab is experimental software and is missing many features, big and small.
Moreover, the computational aspects of category theory are generally
underdeveloped, both theoretically and practically. On the flip side, this means
that there are lots of opportunities to do new and interesting things! Applied
category theory is a young field and is likely to grow significantly.

We welcome contributions and are committed to supporting prospective
contributors, regardless of experience level with category theory. If you are
interested in contributing, please let us know.

## What is Catlab?

Catlab is, or will eventually be, the following things.

**Programming library**: First and foremost, Catlab provides data structures,
algorithms, and serialization for applied category theory. Macros offer a
convenient syntax for specifying categorical doctrines and type-safe symbolic
manipulation systems. Wiring diagrams (aka string diagrams) are supported
through specialized data structures and can be serialized to and from GraphML
(an XML-based format) and JSON.

**Interactive computing environment**: Catlab can also be used interactively in
[Jupyter notebooks](http://jupyter.org). Symbolic expressions are displayed
using LaTeX and wiring diagrams are visualized using
[Compose.jl](https://github.com/GiovineItalia/Compose.jl),
[Graphviz](http://www.graphviz.org), or [TikZ](https://github.com/pgf-tikz/pgf).

**Computer algebra system**: Catlab will serve as a computer algebra system for
categorical algebra. Unlike most computer algebra systems, all expressions are
typed using fragment of dependent type theory called [generalized algebraic
theories](https://ncatlab.org/nlab/show/generalized+algebraic+theory). We will
implement core algorithms for solving word problems and reducing expressions to
normal form with respect to several important doctrines, such as those of
categories and of symmetric monoidal categories. For the computer algebra of
classical abstract algebra, see
[AbstractAlgebra.j](https://github.com/wbhart/AbstractAlgebra.jl) and
[Nemo.jl](https://github.com/wbhart/Nemo.jl).

### What is Catlab not?

Catlab is *not* currently any of the following things, although we do not rule
out that it could eventually evolve in these directions.

**Automated theorem prover**: Although there is some overlap between computer
algebra and automated theorem proving, Catlab cannot be considered a theorem
prover because it does not produce formal certificates of correctness
(aka proofs).

**Proof assistant**: Likewise, Catlab is not a proof assistant because it does
not produce formally verifiable proofs. Formal verification is not within scope
of the project.

**Graphical user interface**: Catlab does not provide a wiring diagram editor
or other graphical user interface. It is primarily a programming library, not a
user-facing application. However, it could be used as the backend for such an
application.

## Contributors ✨

Thanks goes to these wonderful people ([emoji key](https://allcontributors.org/docs/en/emoji-key)):

<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->
<table>
  <tr>
    <td align="center"><a href="https://www.epatters.org"><img src="https://avatars.githubusercontent.com/u/316610?v=4?s=100" width="100px;" alt=""/><br /><sub><b>Evan Patterson</b></sub></a><br /><a href="https://github.com/AlgebraicJulia/Catlab.jl/issues?q=author%3Aepatters" title="Bug reports">🐛</a> <a href="#maintenance-epatters" title="Maintenance">🚧</a> <a href="https://github.com/AlgebraicJulia/Catlab.jl/commits?author=epatters" title="Code">💻</a> <a href="#ideas-epatters" title="Ideas, Planning, & Feedback">🤔</a> <a href="https://github.com/AlgebraicJulia/Catlab.jl/commits?author=epatters" title="Tests">⚠️</a></td>
  </tr>
</table>

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->

This project follows the [all-contributors](https://github.com/all-contributors/all-contributors) specification. Contributions of any kind welcome!
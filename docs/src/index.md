# Catlab.jl Documentation

```@meta
CurrentModule = Catlab
```

Catlab.jl is an experimental framework for applied category theory, written in
[Julia](https://julialang.org). It provides a programming library and
interactive interface for applications of category theory to the sciences and
engineering fields. It emphasizes monoidal categories due to their wide
applicability but can support any categorical doctrine that is formalizable as a
generalized algebraic theory.

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
[Graphviz](http://www.graphviz.org) or [TikZ](https://www.ctan.org/pkg/pgf).

**Computer algebra system**: Catlab will serve as a computer algebra system for
category theory. Unlike most computer algebra systems, all expressions are typed
using fragment of dependent type theory called [generalized algebraic
theories](https://ncatlab.org/nlab/show/generalized+algebraic+theory). We will
implement core algorithms for solving word problems and reducing expressions in
normal form, with respect to several important doctrines, such as the doctrine
of categories and the doctrine of symmetric monoidal categories.

### What is Catlab not?

Catlab is *not* currently any of the following things, although we do not rule
out that it could eventually evolve in these directions.

**Automated theorem prover**: Although there is some overlap between computer
algebra systems and automated theorem provers, Catlab cannot be considered a
theorem prover because it does not produce formal certificates of correctness
(aka proofs).

**Proof assistant**: Likewise, Catlab is not a proof assistant because it does
not produce formally verifiable proofs. Formal verification is not within scope
of the project.

**Graphical user interface**: Catlab does not provide a wiring diagram editor
or other graphical user interface. It is primarily a programming library, not a
user-facing application. However, it could be used as the backend for such an
application.

## Table of Contents

```@contents
Pages = [
     "apis/core.md",
     "apis/doctrines.md",
     "apis/wiring_diagrams.md",
     "apis/graphics.md",
     "apis/programs.md",
     ]
Depth = 2
```

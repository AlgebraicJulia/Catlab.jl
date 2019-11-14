# Catlab.jl Documentation

```@meta
CurrentModule = Catlab
```

Catlab is an experimental library for computational category theory, written in [Julia](https://julialang.org). It aims to provide a programming library and interactive interface for applications of category theory to the mathematical sciences. It emphasizes monoidal categories due to their wide applicability but can support any categorical doctrine that is formalizable as a generalized algebraic theory. An early inspiration for Catlab is the Julia library [Cateno](https://github.com/jasonmorton/Cateno).

**Warning**: This is experimental software. Important features are missing, the API is unstable, and the documentation and examples are sparse. However, it is already useable for some purposes. Contributions are welcome!

## What is it?

Catlab is (or will eventually be!) the following things.

**Programming library**: First and foremost, Catlab provides data structures, algorithms, and serialization for applied category theory. Macros offer a convenient syntax for specifying categorical doctrines and type-safe symbolic manipulation systems. Wiring diagrams (aka string diagrams) are supported through specialized data structures and can be serialized to and from GraphML (an XML-based graph format).

**Interactive computing environment**: Catlab can also be used interactively in [Jupyter notebooks](http://jupyter.org). Symbolic expressions are displayed using LaTeX and wiring diagrams are visualized using [Graphviz](http://www.graphviz.org) or [TikZ](https://www.ctan.org/pkg/pgf). The TikZ wiring diagrams are suitable for publication.

**Computer algebra system**: Catlab will serve as a computer algebra system for category theory. Unlike most computer algebra systems, all expressions are typed using fragment of dependent type theory called [generalized algebraic theories](https://ncatlab.org/nlab/show/generalized+algebraic+theory). We will implement core algorithms for solving word problems and reducing expressions in normal form, with respect to several important doctrines, such as the doctrine of categories and the doctrine of symmetric monoidal categories.

## What is it not?

Catlab is *not* any of the following things. (We do not rule out that Catlab could eventually evolve in these directions but they are not our current focus.)

**Automated theorem prover**: Catlab is not designed to be a general-purpose automated theorem prover for category theory. Under the current plan, its proof capabilities will be confined to carefully circumscribed algebraic problems like normalization and word problems. Also, the system does not produce formal certificates of correctness (aka proofs).

**Proof assistant**: Likewise, Catlab is not a proof assistant because it does not produce formally verifiable proofs.

## Table of Contents
```@contents
Pages = [
     "index.md",
     "apis/index.md",
     "apis/catlab.md",
     "apis/doctrines.md",
     "apis/wiring_diagrams.md",
     "apis/graphics.md",
     "apis/programs.md",
     ]
Depth = 3
```

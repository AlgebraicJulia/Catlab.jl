# Catlab.jl

Catlab.jl is a framework for applied and computational category theory, written
in the [Julia](https://julialang.org) language. Catlab provides a programming
library and interactive interface for applications of category theory to
scientific and engineering fields. It emphasizes monoidal categories due to
their wide applicability but can support any categorical structure that is
formalizable as a generalized algebraic theory.

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
[AbstractAlgebra.jl](https://github.com/wbhart/AbstractAlgebra.jl) and
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
user-facing application. However, there is another project in the AlgebraicJulia
ecosystem, [Semagrams.jl](https://github.com/AlgebraicJulia/Semagrams.jl)
which does provide graphical user interfaces for interacting with wiring
diagrams, Petri nets, and the like.

### What is a GAT?

See [GATlab documentation](https://algebraicjulia.github.io/GATlab.jl)

## Conventions

In several places in Catlab, we use what we call "Abstract Field Convention". Instead of doing the following:

```julia
struct Pair{A}
  x1::A
  x2::A
end

add(xs::Pair) = xs.x1 + xs.x2

const IntPair = Pair{Int}
```

which leads to potentially longer and longer type names as the type parameters increase in size,
we do

```julia
"""
Abstract Fields
- x1::A
- x2::A
"""
abstract type Pair{A} end

add(xs::Pair) = xs.x1 + xs.x2

struct IntPair <: Pair{Int}
  x1::Int
  x2::Int
end
```

That is, we assume that all subtypes of a certain abstract types have the same
field names, and are organized in roughly the same way. There is no way of
enforcing this within Julia, so instead we leave a comment on the abstract type
to document that we are working this way.

Note that this is contrary to the standard wisdom in Julia that one should as
much as possible access structs through methods, not field accesses. The reason
why we do not do this here is twofold. First of all, sometimes it can be
annoying to write out the trivial field-access methods in addition to defining
the struct.  For instance, we have 12 different structs in
`src/acsets/ColumnImplementations.jl` that all are subtypes of an Abstract Field
Convention abstract type. It would be 24 lines of boilerplate to write out the
field accessors for these types with little appreciable benefit. The second
reason is that the Abstract Field Convention is a stronger guarantee than an
interface: we are claiming that any subtype has precisely these fields in this
order, and no others! This is essential for defining methods like copy, which
might be defined as follows.

```julia
function copy(p::T) where {T<:Pair}
  T(p.x1, p.x2)
end
```

So the Abstract Field Convention is stronger than a normal interface. It's not
really about encapsulating data, it's more about cutting down on long names in
debug messages.

## Table of Contents

```@contents
Pages = [
     "apis/theories.md",
     "apis/wiring_diagrams.md",
     "apis/graphics.md",
     "apis/programs.md",
     "devdocs/style.md",
     ]
Depth = 2
```

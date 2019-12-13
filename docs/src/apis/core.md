# Symbolic expressions

```@meta
CurrentModule = Catlab
```

At the core of Catlab is a system for defining and manipulating symbolic
expressions in typed algebraic structures, including categories and monoidal
categories. Objects, morphisms, and even higher-order morphisms are represented
as typed symbolic expressions. The expressions can be manipulated abstractly or
transformed, usually functorially, into more concrete representations, such as
[wiring diagrams](/apis/wiring_diagrams) or [Julia functions](/apis/programs).

The basic elements of this system are:

1. **Signatures** of generalized algebraic theories (GATs), defined using the 
   [`@signature`](@ref) macro. Categories and other typed (multisorted)
   algebraic structures can be defined as GATs.
   
2. **Instances**, or concrete implementations, of signatures, asserted using the
   [`@instance`](@ref) macro.
   
3. **Syntax systems** for signatures, defined using the [`@syntax`](@ref) macro.
   These are type-safe expression trees constructed using ordinary Julia
   functions.

We'll explain each of these elements in greater detail in the following
sections. From the programming perspective, signatures can be thought of as
*interfaces* and bear some resemblance to [type
classes](https://en.wikipedia.org/wiki/Type_class). Both instances and syntax
systems then act as *implementations* of the interface.

## Signatures

[Generalized algebraic
theories](https://ncatlab.org/nlab/show/generalized+algebraic+theory) (GATs) are
the natural logical system in which to define categories and related algebraic
structures. GATs generalize the typed (multisorted) [algebraic
theories](https://ncatlab.org/nlab/show/algebraic+theory) of [universal
algebra](https://en.wikipedia.org/wiki/Universal_algebra) by incorporating a
fragment of dependent type theory; they are perhaps the simplest dependently
typed logics.

Catlab implements a version of the GAT formalism on top of Julia's type system,
taking advantage of Julia macros to provide a pleasant syntax. Signatures of
GATs are defined using the [`@signature`](@ref) macro.

For example, the signature of the theory of categories could be defined by:

```@setup category
using Catlab
import Catlab.Doctrines: Ob, Hom, ObExpr, HomExpr, dom, codom, compose, id
```

```@example category
@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(A::Ob)::Hom(A,A)
  compose(f::Hom(A,B), g::Hom(B,C))::Hom(A,C) <= (A::Ob, B::Ob, C::Ob)
end
nothing # hide
```

The code is simplified only slightly from the official Catlab definition of
`Category`. The signature has two *type constructors*, `Ob` (object) and `Hom`
(morphism). The type `Hom` is a dependent type, depending on two objects, named
`dom` (domain) and `codom` (codomain). The signature has two *term
constructors*, `id` (identity) and `compose` (composition).

Notice how the return types of the term constructors depend on the argument
values. For example, the term `id(A)` has type `Hom(A,A)`. The term constructor
`compose` also uses *context variables*, listed to the right of the `<=` symbol.
This allows us to write `compose(f,g)`, instead of the more verbose
`compose(A,B,C,f,g)` (for discussion, see Cartmell, 1986, Sec 10: Informal
syntax).

!!! note
    
    In general, a GAT consists of a *signature*, defining the types and terms of
    the theory, and a set of *axioms*, the equational laws satisfied by models
    of the theory. The theory of categories, for example, has axioms of
    unitality and associativity. At present, Catlab supports the specification
    of signatures, but not of axioms, reflecting its status as a programming
    library, not a proof assistant. It is the programmer's responsibility to
    ensure any declared instances of an algebraic structure satisfy its axioms.

#### References

- Cartmell, 1986: Generalized algebraic theories and contextual categories,
  [DOI:10.1016/0168-0072(86)90053-9](https://doi.org/10.1016/0168-0072(86)90053-9)
- Cartmell, 1978, PhD thesis: *Generalized algebraic theories and contextual
  categories*
- Pitts, 1995: Categorical logic, Sec 6: Dependent types

## Instances

A signature can have one or more *instances*, or instantiations by ordinary
Julia types and functions. This feature builds on Julia's support for generic
functions with [multiple
dispatch](https://docs.julialang.org/en/v1/manual/methods/).

Instances are declared using the [`@instance`](@ref) macro. In an instance of a
signature, each signature type is mapped to a Julia type and each term is mapped
to a Julia method of the same name. For example, the category of matrices could
be defined as an instance of the signature `Category` defined above:

```@example category
using LinearAlgebra: I

struct MatrixDomain
  eltype::Type
  dim::Int
end

@instance Category(MatrixDomain, Matrix) begin
  dom(M::Matrix) = MatrixDomain(eltype(M), size(M,1))
  codom(M::Matrix) = MatrixDomain(eltype(M), size(M,2))
  
  id(m::MatrixDomain) = Matrix{m.eltype}(I, m.dim, m.dim)
  compose(M::Matrix, N::Matrix) = M*N
end
```

```@example category
A = Matrix{Float64}([0 1; 1 0])
id(dom(A))
```

In this instance, the signature type `Ob` is mapped to the custom Julia type
`MatrixDomain`. The latter type has two fields, a Julia type `eltype`
representing a field $k$ and an integer `dim` representing the dimensionality
$n$, and so can be interpreted as the $n$-dimensional vector space $k^n$. The
signature `Hom` is mapped to the standard Julia type `Matrix`.

## Syntax systems

Signatures can also be instantiated as systems of symbolic expressions, using
the [`@syntax`](@ref) macro. The symbolic expressions are expression trees, as
commonly used in computer algebra systems. They are similar to Julia's `Expr`
type but they are instead subtyped from Catlab's [`GATExpr`](@ref) type and they
have a more refined type hierarchy.

A single signature can have different syntax systems, treating different terms
as primitive or performing different simplication or normalization procedures.
Catlab tries to make it easy to define new syntax systems. Many of the
signatures included with Catlab have default syntax systems, but the user is
encouraged to define their own to suit their needs.

To get started, you can always call the `@syntax` macro with an empty body.
Below, we subtype from Catlab's abstract types `ObExpr` and `HomExpr` to enable
LaTeX pretty-printing and other convenient features, but this is not required.

```@example category
@syntax CategoryExprs(ObExpr, HomExpr) Category begin
end

A, B, C, D = [ Ob(CategoryExprs.Ob, X) for X in [:A, :B, :C, :D] ]
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)

compose(compose(f,g),h)
```

The resulting symbolic expressions perform no simplification. For example, the
associativity law is not satisfied:

```@example category
compose(compose(f,g),h) == compose(f,compose(g,h))
```

Thus, unlike instances of a theory, syntactic expressions are not expected to
obey all the axioms of the theory.

However, the user may supply logic in the body of the `@syntax` macro to enforce
the axioms or perform other kinds of simplification. Below, we use the
[`associate`](@ref) function provided by Catlab to convert the binary
expressions representing composition into $n$-ary expressions for any number
$n$. The option `strict=true` tells Catlab to check that the domain and codomain
objects are strictly equal and throw an error if they are not.

```@example category
@syntax SimplifyingCategoryExprs(ObExpr, HomExpr) Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

A, B, C, D = [ Ob(SimplifyingCategoryExprs.Ob, X) for X in [:A, :B, :C, :D] ]
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)

compose(compose(f,g),h)
```

Now the associativity law *is* satisfied:

```@example category
compose(compose(f,g),h) == compose(f,compose(g,h))
```

### Primitive versus derived operations

In some algebraic structures, there is a choice as to which operations should be
considered primitive and which should be derived. For example, in a [cartesian
monoidal category](https://ncatlab.org/nlab/show/cartesian+monoidal+category),
the copy operation $\Delta_X: X \to X \otimes X$ can be defined in terms of the
pairing operation $\langle f, g \rangle$, or vice versa. In addition, the
projections $\pi_{X,Y}: X \otimes Y \to X$ and $\pi_{X,Y}': X \otimes Y \to Y$
can be defined in terms of the deleting operation (terminal morphism) or left as
primitive.

In Catlab, the recommended way to deal with such situations is to define *all*
the operations in the signature and then allow particular syntax systems to
determine which operations, if any, will be derived from others. In the case of
the cartesian monoidal category, we could define a signature `CartesianCategory`
by inheriting from the builtin signature `SymmetricMonoidalCategory`.

```@setup cartesian-monoidal-category
using Catlab
import Catlab.Doctrines: Ob, Hom, ObExpr, HomExpr, SymmetricMonoidalCategory,
  dom, codom, compose, id, otimes, munit, braid
```

```@example cartesian-monoidal-category
@signature SymmetricMonoidalCategory(Ob,Hom) => CartesianCategory(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  delete(A::Ob)::Hom(A,munit())
  
  pair(f::Hom(A,B), g::Hom(A,C))::Hom(A,otimes(B,C)) <= (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::Hom(otimes(A,B),A)
  proj2(A::Ob, B::Ob)::Hom(otimes(A,B),B)
end
nothing # hide
```

We could then define the copying operation in terms of the pairing.

```@example cartesian-monoidal-category
@syntax CartesianCategoryExprsV1(ObExpr,HomExpr) CartesianCategory begin
  mcopy(A::Ob) = pair(id(A), id(A))
end

A = Ob(CartesianCategoryExprsV1.Ob, :A)
mcopy(A)
```

Alternatively, we could define the pairing and projections in terms of the
copying and deleting operations.

```@example cartesian-monoidal-category
@syntax CartesianCategoryExprsV2(ObExpr,HomExpr) CartesianCategory begin
  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

A, B, C = [ Ob(CartesianCategoryExprsV2.Ob, X) for X in [:A, :B, :C] ]
f, g = Hom(:f, A, B), Hom(:g, A, C)
pair(f, g)
```

## Presentations

TODO

## API

```@autodocs
Modules = [
  GAT,
  Syntax,
  Rewrite,
  Present,
]
Private = false
```

# Syntax and expressions

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

In an instance of a signature, each signature type corresponds to a Julia type
and each term corresponds to a Julia method of that name. For example, the
category of matrices could be defined as the following instance of `Category`,
where the objects are element types $k$ together with a natural number $n$,
representing the $n$-dimensional vector space $k^n$.

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

## Syntax systems

TODO

Unlike instances of a theory, syntactic expressions don't necessarily satisfy
the equations of the theory. For example, the default syntax operations for the
`Category` theory don't form a category because they don't satisfy the category
laws, e.g.,
```
compose(f, id(A)) != compose(f)
```
Whether dependent types are enforced at runtime and whether expressions are
automatically brought to normal form depends on the particular syntax.

## Presentations

TODO

## API

```@autodocs
Modules = [GAT,
           Present,
           Rewrite,
           Syntax,
          ]
```

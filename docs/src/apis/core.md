# Syntax and expressions

```@meta
CurrentModule = Catlab
```

At the core of Catlab is a system for defining and manipulating symbolic
expressions in typed algebraic structures, including categories and monoidal
categories. Objects, morphisms, and even higher-order morphisms are represented
as typed symbolic expressions. The expressions can be manipulated abstractly or
transformed, usually functorially, into more concrete representations, such as
[wiring diagrams](../wiring_diagrams) or [Julia functions](../programs).

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
structures. GATs generalize the typed (multisorted) algebraic theories of
[universal algebra](https://en.wikipedia.org/wiki/Universal_algebra) by
incorporating a fragment of dependent type theory; they are perhaps the simplest
dependently typed logics.

Catlab implements a version of the GAT formalism on top of Julia's type system,
taking advantage of Julia macros to provide a pleasant syntax. Signatures of
GATs are defined using the [`@signature`](@ref) macro.

For example, the signature of the theory of categories could be defined by:

```julia
@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(A::Ob)::Hom(A,A)
  compose(f::Hom(A,B), g::Hom(B,C))::Hom(A,C) <= (A::Ob, B::Ob, C::Ob)
end
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

#### References

- Cartmell, 1986: Generalized algebraic theories and contextual categories,
  [DOI:10.1016/0168-0072(86)90053-9](https://doi.org/10.1016/0168-0072(86)90053-9)
- Pitts, 1995: Categorical logic, Sec 6: Dependent types

## Instances

TODO

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
           Meta,
           Present,
           Rewrite,
           Syntax,
          ]
```

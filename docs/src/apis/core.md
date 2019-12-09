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

We'll explain each of these three elements in the following sections.

## Signatures

TODO: GATs generalize (multisorted) algebraic theories by incorporating a
fragment of dependent type theory. They allow type and term constructors to be
partially defined. GATs provide a convenient formal syntax for categorical
structures.

References:

- (Cartmell, 1986, "Generalized algebraic theories and contextual categoies")
- (Pitts, 1995, "Categorical logic", Sec 6: "Dependent types")

## Instances

TODO

## Syntax systems

TODO: Unlike instances of a theory, syntactic expressions don't necessarily
satisfy the equations of the theory. For example, the default syntax operations
for the `Category` theory don't form a category because they don't satisfy the
category laws, e.g.,
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

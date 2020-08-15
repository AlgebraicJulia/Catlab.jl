# Standard library of theories

Through the module `Catlab.Theories`, Catlab provides a standard library of
[generalized algebraic theories](@ref gats) for categories, monoidal categories,
and other categorical structures. The theories correspond, in most cases, to
standard definitions in category theory and they are used throughout Catlab and
the AlgebraicJulia ecosystem to structure programs and provide a common
interface for applied category theory. The module also provides default [syntax
systems](@ref syntax-systems) for many of the theories.

Categorical structures for which theories are provided include:

+ categories
+ monoidal and symmetric monoidal categories
+ cartesian and cocartesian categories
+ semiadditive categories/biproduct categories
+ hypergraph categories
+ bicategories of relations
+ categories with two monoidal products, such as distributive monoidal
  categories

The contents of this module can be supplemented by the user, and it is even
possible to use many parts of Catlab without using this module. The user is free
to create new syntax systems for the theories defined here and also to define
entirely new theories.

```@autodocs
Modules = [ Theories ]
Private = false
```

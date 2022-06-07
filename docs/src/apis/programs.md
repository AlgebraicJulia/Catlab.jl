# [Programs](@id programs)

The module `Catlab.Programs` provides domain-specific languages (DSLs) for
constructing diagrams of various kinds. The DSLs, implemented as Julia macros,
are based on the syntax of the Julia language but often interpret that syntax
very differently from standard Julia programs. Conversely, this module offers
preliminary support for generating Julia code from wiring diagrams.

There are two major macros for constructing wiring diagrams:

- [`@program`](@ref), for directed wiring diagrams (DWDs)
- [`@relation`](@ref), for undirected wiring diagrams (UWDs)

In addition, there is a family of related macros for constructing
category-theoretic [diagrams](https://ncatlab.org/nlab/show/diagram):

- [`@graph`](@ref), for constructing a graph
- [`@fincat`](@ref), for presenting a category as a graph together with path
  equations
- [`@finfunctor`](@ref), for defining a functor between two finitely presented
  categories
- [`@diagram`](@ref) and [`@free_diagram`](@ref), for defining a diagram in a category

Generalizing the last two macros, the modules provides DSLs for functorial data
migration:

- [`@migrate`](@ref), for migrating data between acsets
- [`@migration`](@ref), for defining data migrations between schemas

## API

```@autodocs
Modules = [
  Programs.GenerateJuliaPrograms,
  Programs.ParseJuliaPrograms,
  Programs.RelationalPrograms,
  Programs.DiagrammaticPrograms,
]
Private = false
```

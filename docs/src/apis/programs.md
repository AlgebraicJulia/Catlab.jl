# [Programs](@id programs)

The module `Catlab.Programs` provides domain-specific languages (DSLs) for
constructing diagrams of various kinds. The DSLs, implemented as Julia macros,
are based on the syntax of the Julia language but often interpret that syntax
very differently from standard Julia programs. Conversely, this module offers
preliminary support for generating Julia code from wiring diagrams.

There are two major macros for constructing wiring diagrams:

- [`@program`](@ref), for directed wiring diagrams (DWDs)
- [`@relation`](@ref), for undirected wiring diagrams (UWDs)

There is a family of related macros for constructing
category-theoretic [diagrams](https://ncatlab.org/nlab/show/diagram) included in `AlgebraicDataMigrations.jl`.

## API

```@autodocs
Modules = [
  Programs.GenerateJuliaPrograms,
  Programs.ParseJuliaPrograms,
  Programs.RelationalPrograms
]
Private = false
```

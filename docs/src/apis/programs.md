# [Programs](@id programs)

The module `Catlab.Programs` provides domain-specific languages (DSLs) for
constructing diagrams of various kinds. The DSLs, implemented as Julia macros,
are based on Julia syntax but often interpret that syntax very differently from
standard Julia programs. In the other direction, the module also offers limited
facilities for generating Julia code from wiring diagrams.

There are two major macros for constructing wiring diagrams:

- [`@program`](@ref), for directed wiring diagrams
- [`@relation`](@ref), for undirected wiring diagrams

## API

```@autodocs
Modules = [
  Programs.GenerateJuliaPrograms,
  Programs.ParseJuliaPrograms,
  Programs.RelationalPrograms,
]
Private = false
```

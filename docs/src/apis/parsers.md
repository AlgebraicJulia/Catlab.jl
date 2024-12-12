# [Parsers](@id parsers)

This module `Catlab.Parsers` provides parsing expression grammars to support domain-specific languages (DSLs) for
constructing diagrams of various kinds. The DSLs, implemented as Julia string macros,
are based on the syntax of their `Catlab.Programs` counterparts which are based on the
syntax of the Julia language but often interpret that syntax
very differently from standard Julia programs.

As of now, there is currently only one parsing expression grammar for constructing wiring diagrams:

- [`relation_str`](@ref) for constructing undirected wiring diagrams.

## API

```@autodocs
Modules = [
  Parsers.ParserCore,
  Parsers.RelationalParser
]
Private = false
```

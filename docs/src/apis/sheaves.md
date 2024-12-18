# [Sheaves](@id sheaves)

Sheaves are useful for modeling spatial data. The classic example is continuous functions over a topological space. If you have a function defined at every point in a topological space, then you can think about covers of your space and how that function restricts to subspaces of their domain. When you have locally defined functions that agree on overlapping domains, you can extend them to one function defined on the union of their domains.

Sheaves are a generalization of this idea. The motivating example of sheaves of vectors is implemented and described in the vignettes.

```@autodocs
Modules = [
  Sheaves
  ]
```

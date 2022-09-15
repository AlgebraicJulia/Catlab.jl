# [Categorical algebra](@id categorical_algebra)

## Sets and Relations

The following APIs implement FinSet, the category of Finite Sets (actually the skeleton of FinSet). The objects of this category are natural numbers where `n` represents a set with `n` elements. The morphisms are functions between such sets. We use the skeleton of FinSet in order to ensure that all sets are finite and morphisms can be stored using lists of integers. Finite relations are built out of FinSet and can be used to do some relational algebra.

```@autodocs
Modules = [
  CategoricalAlgebra.Sets,
  CategoricalAlgebra.FinSets,
  CategoricalAlgebra.FinRelations,
  ]
Private = false
```

## Free Diagrams, Limits, and Colimts

The following modules define free diagrams in an arbitrary category and specify limit and colimt cones over said diagrams. Thes constructions enjoy the fullest support for FinSet and are used below to define presheaf categories as C-Sets. The general idea of these functions is that you set up a limit computation by specifying a diagram and asking for a limit or colimit cone, which is returned as a struct containing the apex object and the leg morphisms. This cone structure can be queried using the functions [`apex`](@ref) and [`legs`](@ref). Julia's multiple dispatch feature is heavily used to specialize limit and colimit computations for various diagram shapes like product/coproduct and equalizer/coequalizer. As a consumer of this API, it is highly recommended that you use multiple dispatch to specialize your code on the diagram shape whenever possible.

```@autodocs
Modules = [
  CategoricalAlgebra.FreeDiagrams,
  CategoricalAlgebra.Limits,
  ]
Private = false
```

## Categories

```@autodocs
Modules = [
   CategoricalAlgebra.Categories,
   CategoricalAlgebra.FinCats,
]
```

## Acsets

### Overview and Theory

For an in depth look into the theory behind acsets, we refer the reader to [our paper](https://arxiv.org/abs/2106.04703) on the subject, which also gives some sense as to how the implementation works. Here, we give a brief tutorial before the the API documentation.

The most essential part of the acset machinery is the schema. The schema *parameterizes* the acset: each schema corresponds to a different type of acset. Schemas consist of four parts.

- Objects $$X,Y$$ (`(X,Y,Z)::Ob`)
- Homomorphisms $$f \colon X \to Y$$ (`f :: Hom(X,Y)`), which go from objects to objects
- Attribute types $$\mathtt{T}$$ (`T :: AttrType`)
- Attributes $$a \colon X \to \mathtt{T}$$ (`a :: Attr(X,T)`), which go from objects to data types

For those with a categorical background, a schema is a presentation of a category $$|S|$$ along with a functor $$S$$ from $$|S|$$ to the arrow category $$0 \to 1$$, such that $$S^{-1}(1)$$ is discrete.

An acset $$F$$ on a schema consists of...

- a set $$F(X)$$ of "primary keys" for each object
- a function $$F(f) \colon F(X) \to F(Y)$$ for each morphism
- a Julia data type $$F(\mathtt{T})$$ for each data type $$\mathtt{T}$$
- a function $$F(a) \colon F(X) \to F(\mathtt{T})$$ for each attribute $$a$$.

For those with a categorical background, an acset on a schema $$S$$ consists of a functor from $$S$$ to $$\mathsf{Set}$$, such that objects in $$S^{-1}(0)$$ map to finite sets, and objects in $$S^{-1}(1)$$ map to sets that represent types. For any particular functor $$K \colon S^{-1}(1) \to \mathsf{Set}$$, we can also take the category of acsets that restrict to this map on $$S^{-1}$$.

We can also add equations to this presentation, but we currently do nothing with those equations in the implementation; they mostly serve as documentation.

We will now give an example of how this all works in practice.

```@example
using Catlab, Catlab.CategoricalAlgebra

# Write down the schema for a weighted graph
@present SchWeightedGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
  T::AttrType
  weight::Attr(E,T)
end

# Construct the type used to store acsets on the previous schema
# We *index* src and tgt, which means that we store not only
# the forwards map, but also the backwards map.
@acset_type WeightedGraph(SchWeightedGraph, index=[:src,:tgt])

# Construct a weighted graph, with floats as edge weights
g = @acset WeightedGraph{Float64} begin
  V = 4
  E = 5
  src = [1,1,1,2,3]
  tgt = [2,3,4,4,4]
  weight = [7.2, 9.3, 9.4, 0.1, 42.0]
end
```

### API

The mathematical abstraction of an acset can of course be implemented in many different ways. Currently, there are three implementations of acsets in Catlab, which share a great deal of code.

These implementations can be split into two categories.

The first category is **static acset types**. In this implementation, different schemas correspond to different Julia types. Methods on these Julia types are then custom-generated for the schema, using [CompTime.jl](https://github.com/AlgebraicJulia/CompTime.jl).

Under this category, there are two classes of static acset types. The first class is acset types that are generated using the `@acset_type` macro. These acset types are custom-derived structs. The advantage of this is that the structs have names like `Graph` or `WiringDiagram` that are printed out in error messages. The disadvantage is that if you are taking in schemas at runtime, you have to `eval` code in order to use them.

Here is an example of using `@acset_type`

```julia
@acset_type WeightedGraph(SchWeightedGraph, index=[:src,:tgt])
g = WeightedGraph()
```

The second class is `AnonACSet`s. Like acset types derived from `@acset_type`, these contain the schema in their type. However, they also contain the type of their fields in their types, so the types printed out in error messages are long and ugly. The advantage of these is that they can be used in situations where the schema is passed in at runtime, and they don't require using `eval` to create a new acset type.

Here is an example of using `AnonACSet`

```julia
const WeightedGraph = AnonACSetType(SchWeightedGraph, index=[:src,:tgt])
g = WeightedGraph()
```

The second category is **dynamic acset types**. Currently, there is just one type that falls under this category: `DynamicACSet`. This type has a **field** for the schema, and no code-generation is done for operations on acsets of this type. This means that if the schema is large compared to the data, this type will often be faster than the static acsets.

However, dynamics acsets are a new addition to Catlab, and much of the machinery of limits, colimits, and other high-level acset constructions assumes that the schema of an acset can be derived from the type. Thus, more work will have to be done before dynamic acsets become a drop-in replacement for static acsets.

Here is an example of using a dynamic acset

```julia
g = DynamicACSet("WeightedGraph", SchWeightedGraph; index=[:src,:tgt])
```

```@autodocs
Modules = [
  CategoricalAlgebra.CSets,
  CategoricalAlgebra.StructuredCospans,
  CategoricalAlgebra.ACSetInterface,
  CategoricalAlgebra.ACSetColumns,
  CategoricalAlgebra.CSetDataStructures
]
Private = false
```

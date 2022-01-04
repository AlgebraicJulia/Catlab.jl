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

We can also add relations to this presentation, but we currently do nothing with those relations in the implementation; they mostly serve as documentation.

We will now give an example of how this all works in practice.

```@example
using Catlab, Catlab.CategoricalAlgebra

# Write down the schema for a weighted graph
@present TheoryWeightedGraph(FreeSchema) begin
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
@acset_type WeightedGraph(TheoryWeightedGraph, index=[:src,:tgt])

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

We first give an overview of the data types used in the acset machinery.

`FreeSchema` A finite presentation of a category that will be used as the schema of a database in the *algebraic databases* conception of categorical database theory. Functors out of a schema into FinSet are combinatorial structures over the schema. Attributes in a schema allow you to encode numerical (any julia type) into the database. You can find several examples of schemas in `Catlab.Graphs` where they define categorical versions of graph theory.

`CSet/AttributedCSet` is a struct/constructors whose values (tables, indices) are parameterized by a CatDesc/AttrDesc. These are in memory databases over the schema equiped with `ACSetTranformations` as natural transformations that encode relationships between database instances.

`CSetType/AttributedCSetType`provides a function to construct a julia type for ACSet instances, parameterized by CatDesc/AttrDesc. This function constructs the new type at runtime. In order to have the interactive nature of Julia, and to dynamically construct schemas based on runtime values, we need to define new Julia types at runtime. This function converts the schema spec to the corresponding Julia type.

`CatDesc/AttrDesc` the encoding of a schema into a Julia type. These exist because Julia only allows certain kinds of data in the parameter of a dependent type. Thus, we have to serialize a schema into those primitive data types so that we can use them to parameterize the ACSet type over the schema. This is an implementation detail subject to complete overhaul.


```@autodocs
Modules = [
  CategoricalAlgebra.CSets,
  CategoricalAlgebra.StructuredCospans,
  CategoricalAlgebra.ACSetInterface,
]
Private = false
```

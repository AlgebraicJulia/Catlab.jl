# Release Notes

## Migration guide for `v<0.16` to `v0.17`

> Note: this document will be updated as more packages in the AlgebraicJulia ecosystem are brought up to speed with `v0.17`.

This major release comes with a variety of breaking changes. This guide provides some general advice for getting code which had worked with `v0.16` to work with `v0.17`. The difficulty of migrating the code can vary depending on how deep one's code reaches into Catlab's internals. We start with some easy fixes that should apply to most uses of Catlab:

### Interacting with ACSets

#### `ThACSetCategory` implementations

The main change with ACSets is that that we do not infer from the ACSet itself (or its morphisms) what kind of category of ACSets we are working with. Although we can make educated guesses sometimes, this is in principle extra data that must be supplied whenever working with ACSets categorically. There are a variety of `ThACSetCategory` implementations which Catlab comes with:

| Implementation | Has attributes | Mark as Deleted | Has attribute variables | Julia functions in components[^1] |
|:--:|:--:|:--:|:--:|:--:|
| `CSetCat` | $\times$ | $\times$ | $\times$ | $\times$ |
| `ACSetCat` | $\checkmark$ | $\times$ | $\times$ | $\times$ |
| `MADCSetCat` | $\times$ | $\checkmark$ | $\times$ | $\times$ |
| `MADACSetCat` | $\checkmark$ | $\checkmark$ | $\times$ | $\times$ |
| `VarACSetCat` | $\checkmark$ | $\times$ | $\checkmark$ | $\times$ |
| `MADVarACSetCat` | $\checkmark$ | $\checkmark$ | $\checkmark$ | $\times$ |
| `LooseACSetCat` | $\checkmark$ | $\times$ | $\times$ | $\checkmark$ |

[^1]: Almost always, when attributes are involved, we want maps between ACSets to preserve the attributes on the nose. However, in the category with "loose ACSetTransformations", we allow maps between ACSets to include the data of a Julia function is not the identity function for some type.


Each of these takes in an (arbitrary) `ACSet` of the kind one wishes to work with. We then wrap the implementation of  `ThACSetCategory` with its designated wrapper type: `ACSetCategory`.

```julia
const 𝒞 = ACSetCategory(CSetCat(Graph()))
```

#### Calling methods with `ThACSetCategory` implementations

Now we can use this piece of data as a parameter for various ACSet-related operations. Presently this can happen in two ways, depending on whether the method we are using belongs to a formal interface (via GATlab) or not. For example, if we call `methods(coproduct)` we'll see a method whose first argument is `GATlab.WithModel`. This indicates that we should use `coproduct` like the following:

```julia
G2 = ob(coproduct[𝒞](Graph(1), Graph(1))) # instead of: ob(coproduct(Graph(1), Graph(1)))
```

Other methods haven't yet been put into a formal interface. E.g. `is_natural` and `homomorphism` do not have a `WithModel` parameter, though they do take keyword arguments. In such cases, `homomorphism(X,Y; cat=𝒞)` is how we signal which category we want to work in.[^2] 

[^2]: If the `cat` kwarg is not provided, most methods will do their best to silently infer what the right category to work in is, based on the ACSet argument provided.

The hardest place to insert this extra parameter is binary operators like `⊕`. These can't be modified with the indexing notation. This is where the `@withmodel` macro is helpful.

```julia
@withmodel TypedCatWithCoproducts(𝒞) (⊕) begin
  @test is_isomorphic(G2, Graph(1) ⊕ Graph(1))
end
```

As you can see, we presently need to wrap `𝒞` with `TypedCatWithCoproducts` for this to work. For subobject connectives like `∧`, one can use `𝒞` directly.

#### Interacting with category interface

One thing we do with morphisms (including `ACSetTransformations`) is compose them. This is now parameterized by a choice of implementation of `ThCategory`. Our `𝒞` from above should be used as a model parameter for `compose` and `id`.

```julia
f = ACSetTransformation(G2, Graph(1); V=[1,1], cat=𝒞)
f′ = compose[𝒞](id[𝒞](G2), f)
```

#### Extensional equality and `force`

There are many granularities of equality that one may be interested in. `==` is quite coarse: `f` and `f′` above are not equal under that equivalence relation. However, under `≃` (an operator introduced in `v0.17`) they are equal. This should be used in place of `force(f) == force(f′)`. 

`force` can be used to improve the performance of a function by replacing it with an equivalent-behavior one, but this is not always a normal form for comparison of extensional behavior (e.g. `id(FinSet(100))` when converted to a normal form is much less efficient than just leaving it as an `IdentityFunction`).


### Other changes

#### General

- Pretty printing may have changed, and some things that previously were pretty printed may not be presently pretty printed at all. This can be fixed piecemeal in the future.

#### SetFunctions/FinFunctions 

- Functions (e.g. `FinFunction`) previously were able to be applied to a vector, which was taken to mean it should be mapped over its elements. Now, because the function may have a domain which includes vectors as elements, this mapping behavior is best done using Julia's dot notation

```julia 
f = FinFunction([3,2,1], 3)
f(1) == 3
f.([1,1,3,2]) == [3,3,1,2] # instead of: f([1,1,3,2])
```

- It is no longer the case that `FinFunction` has type parameters for the type of its (co)domain sets. One can get these in a way generic to any implementation of any theory, i.e. `impl_type(my_finfunction, :Dom)`. Likewise, types in the set hierarchy (`FinSet`, `SetOb`) do not have type parameters. These are all wrapper types around models of a particular theory.

- Catlab no longer infers the codomain of a FinFunction presented by just a vector.

```julia
FinFunction([1,2,4], 4) # instead of: FinFunction([1,2,4])
```

- `TypeSet(T::Type)` is now an *implementation* of `ThSet` (something which could be wrapped by `SetOb`), *not* a `SetOb` itself. Old code which explicitly uses `TypeSet(T)` will likely not work, so instead one should use `SetOb(T)` which is defined to be `SetOb(TypeSet(T))`. Likewise, `ConstantFunction` is not a function but an *implementation* of `ThSetFunction`. In this case, however, one must manually apply the wrapper type:

```julia
# Previously:
# c = ConstantFunction("foo", TypeSet(Int))
# (dom(c), codom(c)) == (TypeSet(Int), TypeSet(String))

c = SetFunction(ConstantFunction("foo", SetOb(Int)))
(dom(c), codom(c)) == (SetOb(Int), SetOb(String))
```

- There may be subtle differences in how indexing of functions works with composing (e.g. if you (pre/post)compose an indexed `FinFunctionVector` with some other implementation of `FinFunction`, is the result indexed?). Trying to make this more systematic or predictable is future work.

#### FreeDiagrams

`FreeDiagram` is now the wrapper type for implementations of the `ThFreeDiagram` interface. What was previously called `FreeDiagram` is now called `FreeGraph` (it is itself one particular implementation of `ThFreeDiagram`). 

Now that `(co)dom` are model-parameterized methods which are called within the constructor of multi(co)spans, one can pass a `cat` keyword argument to these constructors. Alternatively, one can provide the feet of the span as a vector as well, in which case `(co)dom` will not be called when constructing the multi(co)span.

#### FinCats / FinDomFunctors

There have been subtle changes to the `FinCat` and `Fin(Dom)Functor` constructors, as the previous code really presupposed there are only two types of FinCats (graph-like ones with integers as objects and schema-like ones with symbols/presentation generators as objects). We now have FinFunctors which work with anything which implements `ThFinCat` (which could in principle be done with any Julia types for `Ob` and `Hom`), but the tradeoff is that things that were once unambiguous become ambiguous and more data is required to be specified. For example, one previously could define a `FinFunctor` via an object mapping, a hom mapping, a source schema, and a target schema. Presently, one should be more explicit: plugging in `FinCat`s for the (co)domain and using the actual objects/homs of that category in the mappings (which happen to GAT generators, not symbols). 

```julia
# Previously: 
# F = FinFunctor(Dict(:V => :El, :E => :Arr), Dict(:src => :src, :tgt => :tgt),
#                 SchGraph, SchElements)
V, E, src, tgt = generators(SchGraph)
El, Arr, _, _, src′, tgt′, _ = generators(SchElements)
src, tgt = 
F = FinFunctor(Dict(V => El, E => Arr), Dict(src => src′, tgt => tgt′),
                FinCat(SchGraph), FinCat(SchElements); homtype=:generator)
```

Another difference is the `homtype` keyword argument. If the codomain is itself 
a `FinCat`, it has both `Hom` and `Gen` Julia types associated with itself. 
Therefore we can talk about `Hom`s in the codomain category in one of 
the four following:

- `:hom`: give an element of `Hom` directly
- `:generator`: give an element of `Gen` directly (coerce via `to_hom(cod, f)`)
- `:list`: give a *nonempty* list of composable `Gen` (coerce via `compose[cod](to_hom.(cod, f))`)
- `:path`: give a `Path` of composable `Gen` (where `Path` enforces composability + also allows representing id maps)

Previously `hom_map(F, f)` was used *both* to apply `F` to generators and homs in the domain of a `Fin(Dom)Functor`. To do so now would be ambiguous behavior (if `DomGen` and `DomHom` are the same Julia type), so `gen_map` is new a method one can call.

The `ob_generators` and `hom_generators` methods for a `FinCat` now each return a `FinSet` rather than an `AbstractVector`.

#### Module structure

Because the module structure of CategoricalAlgebra has changed, some code that makes reference to this module structure will need to be fixed:

```julia
using CategoricalAlgebra.Cats.FinCats, # instead of : using CategoricalAlgebra.FinCats
```

The main change is that `CategoricalAlgebra` got split into four pieces: `BasicSets` along with four submodules of the new `CategoricalAlgebra` (`Cats`, `SetCats`, `Pointwise`, and `Misc`).

### Regressions

The `HomomorphismQuery` option for computing all the full hom set between two ACSets via a limit computation is currently not yet re-implemented in `v0.17`. This code is quite complex and will take some time to redo in the future.

The category of ACSets and LooseACSetTransformations now is defined as having SetFunctions between TypeSets as the category for its attribute types. This means a certain kind of pullback of LooseACSetTransformations (where the components map between *finite sets*, rather than `TypeSet`s) is no longer supported. 

### Performance regressions

Performance regressions can be introduced in this migration by naive use of the `method[model](args...)` idiom. This is because this pattern uses dynamic dispatch and as such shouldn't be used in hot loops. If one wants to call a method associated with an interface in a more performant manner, the following style is required:

```julia
compose(WithModel(my_cat), f, g) # clunkier, but better performance than: compose[my_cat](f,g)
```

Also note the type of `my_cat` must be known statically.

### Example migration: AlgebraicPetri 

The process of updating [AlgebraicPetri.jl](https://github.com/AlgebraicJulia/AlgebraicPetri.jl) to work with Catlab 0.17 was addressed in [this PR](https://github.com/AlgebraicJulia/AlgebraicPetri.jl/pull/181). The required changes were:

- No more `LooseACSetTransformation`: instead stratification limits are in a `LooseACSet` category of ACSets.
- Some uses of `==` in the tests replaced with `≃`.
- Components of ACSetTransformations no longer assumed to be `FinFunctionVector`: to get a vector out of a `FinFunction` we now call `collect(f)` instead of `f.func`.
- `FinDomFunction` ob/hom mappings use presentation generators, not symbols.

There was one logic error in the previous implementation that was revealed in the update process: when we call `flatten_labels` to take a stratified model (which has, for example, `Name` attributes valued in *pairs* of symbols) and convert it to a regular Petri net (`Name` valued in just symbols with a `_` in the middle of the pair), the code previously did not change the components of typing hom that is going out of the model into a typing petri net. This needed to be fixed because otherwise a type error would be encountered (trying to use a function with domain `Tuple{String,String}`  when a function with domain `String` was needed).
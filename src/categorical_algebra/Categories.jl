""" 2-category of categories, functors, and natural transformations.

Categories in mathematics appear in the large, often as categories of sets with
extra structure, and in the small, as algebraic structures that generalize
groups, monoids, preorders, and graphs. This division manifests in Catlab as
well. Large categories (in spirit, if not in the [technical
sense](https://ncatlab.org/nlab/show/large+category)) occur throughout Catlab as
`@instance`s of the theory of categories. For computational reasons, small
categories are usually presented by generators and relations.

This module provides a minimal interface to accomodate both situations. Category
instances are supported through the wrapper type [`TypeCat`](@ref). Finitely
presented categories are provided by another module, [`FinCats`](@ref).
"""
module Categories
export Cat, TypeCat, Functor, Transformation, dom, codom, compose, id,
  ob, hom, is_hom_equal, ob_map, hom_map, dom_ob, codom_ob, component,
  OppositeCat, op, co

using AutoHashEquals

using ...GAT
import ...Theories: Category2, ob, hom, dom, codom, compose, ⋅, ∘, id,
  composeH, *

# Categories
############

""" Size of a category, used for dispatch and subtyping purposes.

A [`Cat`](@ref) type having a particular `CatSize` means that categories of that
type are *at most* that large.
"""
abstract type CatSize end

""" Size of a large category, such as Set.

To the extent that they form a category, we regard Julia types and functions
([`TypeCat`](@ref)) as forming a large category.
"""
struct LargeCatSize <: CatSize end

""" Abstract base type for a category.

The objects and morphisms in the category have Julia types `Ob` and `Hom`,
respectively. Note that these types do *not* necessarily form an `@instance` of
the theory of categories, as they may not meaningfully form a category outside
the context of this object. For example, a finite category regarded as a
reflexive graph with a composition operation might have type `Cat{Int,Int}`,
where the objects and morphisms are numerical identifiers for vertices and edges
in the graph.

The basic operations available in any category are: [`dom`](@ref),
[`codom`](@ref), [`id`](@ref), [`compose`](@ref).
"""
abstract type Cat{Ob,Hom,Size<:CatSize} end

""" Coerce or look up object in category.

Converts the input to an object in the category, which should be of type `Ob` in
a category of type `Cat{Ob,Hom}`. How this works depends on the category, but a
common case is to look up objects, which might be integers or GAT expressions,
by their human-readable name, usually a symbol.

See also: [`hom`](@ref).
"""
function ob end

""" Coerce or look up morphism in category.

See also: [`ob`](@ref).
"""
function hom end

""" Domain of morphism in category.
"""
dom(C::Cat, f) = dom(f)

""" Codomain of morphism in category.
"""
codom(C::Cat, f) = codom(f)

""" Identity morphism on object in category.
"""
id(C::Cat, x) = id(x)

""" Compose morphisms in a category.
"""
compose(C::Cat, fs...) = compose(fs...)

""" Are two morphisms in a category equal?

By default, just checks for equality of Julia objects using ``==``. In some
categories, checking equality of morphisms may involve nontrivial reasoning.
"""
is_hom_equal(C::Cat, f, g) = is_hom_equal(f, g)
is_hom_equal(f, g) = f == g

# Instances
#----------

""" Pair of Julia types regarded as a category.

The Julia types should form an `@instance` of the theory of categories
(`Theories.Category`).
"""
struct TypeCat{Ob,Hom} <: Cat{Ob,Hom,LargeCatSize} end

TypeCat(Ob::Type, Hom::Type) = TypeCat{Ob,Hom}()

# FIXME: Type conversion isn't practical because types are often too tight.
#ob(::TypeCat{Ob,Hom}, x) where {Ob,Hom} = convert(Ob, x)
#hom(::TypeCat{Ob,Hom}, f) where {Ob,Hom} = convert(Hom, f)
ob(::TypeCat, x) = x
hom(::TypeCat, f) = f

Base.show(io::IO, ::TypeCat{Ob,Hom}) where {Ob,Hom} =
  print(io, "TypeCat($Ob, $Hom)")

# Functors
##########

""" Abstract base type for a functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Cat`](@ref)), so when writing generic
code one should prefer the `ob_map` and `hom_map` functions.
"""
abstract type Functor{Dom<:Cat,Codom<:Cat} end

""" Evaluate functor on object.
"""
@inline ob_map(F::Functor, x) = do_ob_map(F, x)

""" Evaluate functor on morphism.
"""
@inline hom_map(F::Functor, f) = do_hom_map(F, f)

""" Identity functor on a category.
"""
@auto_hash_equals struct IdentityFunctor{Dom<:Cat} <: Functor{Dom,Dom}
  dom::Dom
end

codom(F::IdentityFunctor) = F.dom

do_ob_map(F::IdentityFunctor, x) = ob(F.dom, x)
do_hom_map(F::IdentityFunctor, f) = hom(F.dom, f)

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  show_domains(io, F, codomain=false)
  print(io, ")")
end

""" Composite of functors.
"""
@auto_hash_equals struct CompositeFunctor{Dom,Codom,
    F<:Functor{Dom,<:Cat},G<:Functor{<:Cat,Codom}} <: Functor{Dom,Codom}
  fst::F
  snd::G
end
Base.first(F::CompositeFunctor) = F.fst
Base.last(F::CompositeFunctor) = F.snd

dom(F::CompositeFunctor) = dom(first(F))
codom(F::CompositeFunctor) = codom(last(F))

do_ob_map(F::CompositeFunctor, x) = ob_map(F.snd, ob_map(F.fst, x))
do_hom_map(F::CompositeFunctor, f) = hom_map(F.snd, hom_map(F.fst, f))

function Base.show(io::IO, F::CompositeFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end

show_type_constructor(io::IO, ::Type{<:Functor}) = print(io, "Functor")

function show_domains(io::IO, f; domain::Bool=true, codomain::Bool=true,
                      recurse::Bool=true)
  if get(io, :hide_domains, false)
    print(io, "…")
  else
    if domain
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
    end
    if codomain
      domain && print(io, ", ")
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
    end
  end
end

# Callables
#----------

Functor(f::Function, g::Function, C::Cat, D::Cat) = FunctorCallable(f, g, C, D)

""" Functor defined by two Julia callables, an object map and a morphism map.
"""
@auto_hash_equals struct FunctorCallable{Dom,Codom} <: Functor{Dom,Codom}
  ob_map::Any
  hom_map::Any
  dom::Dom
  codom::Codom
end

dom(F::FunctorCallable) = F.dom
codom(F::FunctorCallable) = F.codom
do_ob_map(F::FunctorCallable, x) = F.ob_map(x)
do_hom_map(F::FunctorCallable, f) = F.hom_map(f)

# Instances
#----------

(F::Functor{TypeCat{Ob,Hom}})(x::Ob) where {Ob,Hom} = ob_map(F, x)
(F::Functor{TypeCat{Ob,Hom}})(f::Hom) where {Ob,Hom} = hom_map(F, f)

# Natural transformations
#########################

""" Abstract base type for a natural transformation between functors.

A natural transformation ``α: F ⇒ G`` has a domain ``F`` and codomain ``G``
([`dom`](@ref) and [`codom`](@ref)), which are functors ``F,G: C → D`` having
the same domain ``C`` and codomain ``D``. The transformation consists of a
component ``αₓ: Fx → Gx`` in ``D`` for each object ``x ∈ C``, accessible using
[`component`](@ref) or indexing notation (`Base.getindex`).
"""
abstract type Transformation{C<:Cat,D<:Cat,Dom<:Functor,Codom<:Functor} end

""" Component of natural transformation.
"""
function component end

@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

@auto_hash_equals struct IdentityTransformation{C<:Cat,D<:Cat,Dom<:Functor{C,D}} <:
     Transformation{C,D,Dom,Dom}
  dom::Dom
end

codom(α::IdentityTransformation) = α.dom

function component(α::IdentityTransformation, x)
  F = dom(α)
  id(codom(F), ob_map(F, x))
end

const IdIdTransformation{C<:Cat} = IdentityTransformation{C,C,IdentityFunctor{C}}

# 2-category of categories
##########################

@instance Category2{Cat,Functor,Transformation} begin
  dom(F::Functor) = F.dom
  codom(F::Functor) = F.codom
  id(C::Cat) = IdentityFunctor(C)

  function compose(F::Functor, G::Functor; strict::Bool=true)
    !strict || codom(F) == dom(G) ||
      error("Domain mismatch in composition $F ⋅ $G")
    compose_id(F, G)
  end

  dom(α::Transformation) = α.dom
  codom(α::Transformation) = α.codom
  id(F::Functor) = IdentityTransformation(F)

  function compose(α::Transformation, β::Transformation; strict::Bool=true)
    !strict || codom(α) == dom(β) ||
      error("Domain mismatch in vertical composition $α ⋅ $β")
    compose_id(α, β)
  end
  function composeH(α::Transformation, β::Transformation; strict::Bool=true)
    !strict || codom_ob(α) == dom_ob(β) ||
      error("Domain mismatch in horizontal composition $α * $β")
    composeH_id(α, β)
  end
  function composeH(α::Transformation, H::Functor; strict::Bool=true)
    !strict || codom_ob(α) == dom(H) ||
      error("Domain mismatch in whiskering $α * $H")
    composeH_id(α, H)
  end
  function composeH(F::Functor, β::Transformation; strict::Bool=true)
    !strict || codom(F) == dom_ob(β) ||
      error("Domain mismatch in whiskering $F * $β")
    composeH_id(F, β)
  end
end

# XXX: Is this normalization of identities using multiple dispatch a good idea?
# Unlike in `Sets`, it doesn't feel great since it requires so much boilerplate.

@inline compose_id(F::Functor, G::Functor) = do_compose(F, G)
@inline compose_id(F::Functor, ::IdentityFunctor) = F
@inline compose_id(::IdentityFunctor, G::Functor) = G
@inline compose_id(F::IdentityFunctor, ::IdentityFunctor) = F

@inline compose_id(α::Transformation, β::Transformation) = do_compose(α, β)
@inline compose_id(α::Transformation, ::IdentityTransformation) = α
@inline compose_id(::IdentityTransformation, β::Transformation) = β
@inline compose_id(α::IdentityTransformation, ::IdentityTransformation) = α

@inline composeH_id(α::Transformation, β::Transformation) = do_composeH(α, β)
@inline composeH_id(α::Transformation, ::IdIdTransformation) = α
@inline composeH_id(::IdIdTransformation, β::Transformation) = β
@inline composeH_id(α::IdIdTransformation, ::IdIdTransformation) = α

@inline composeH_id(α::Transformation, H::Functor) = do_composeH(α, H)
@inline composeH_id(α::Transformation, ::IdentityFunctor) = α
@inline composeH_id(α::IdentityTransformation, H::Functor) =
  id(compose_id(dom(α), H))
@inline composeH_id(α::IdentityTransformation, ::IdentityFunctor) = α

@inline composeH_id(F::Functor, β::Transformation) = do_composeH(F, β)
@inline composeH_id(::IdentityFunctor, β::Transformation) = β
@inline composeH_id(F::Functor, β::IdentityTransformation) =
  id(compose_id(F, dom(β)))
@inline composeH_id(::IdentityFunctor, β::IdentityTransformation) = β

do_compose(F::Functor, G::Functor) = CompositeFunctor(F, G)

@inline function do_composeH(α::Transformation, β::Transformation)
  do_composeH(α, β, Val{:covariant})
end
function do_composeH(α::Transformation, β::Transformation,
                     ::Type{Val{:covariant}})
  G, H = codom(α), dom(β)
  compose_id(composeH_id(α, H), composeH_id(G, β))
end
function do_composeH(α::Transformation, β::Transformation,
                     ::Type{Val{:contravariant}})
  F, K = dom(α), codom(β)
  compose_id(composeH_id(F, β), composeH_id(α, K))
end

# Oppositization 2-functor
#-------------------------

""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@auto_hash_equals struct OppositeCat{Ob,Hom,Size<:CatSize,C<:Cat{Ob,Hom,Size}} <:
    Cat{Ob,Hom,Size}
  cat::C
end

ob(C::OppositeCat, x) = ob(C.cat, x)
hom(C::OppositeCat, f) = hom(C.cat, f)

dom(C::OppositeCat, f) = codom(C.cat, f)
codom(C::OppositeCat, f) = dom(C.cat, f)
id(C::OppositeCat, x) = id(C.cat, x)
compose(C::OppositeCat, f, g) = compose(C.cat, g, f)

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::Functor)` instead of directly instantiating this type.
"""
@auto_hash_equals struct OppositeFunctor{C,D,F<:Functor{C,D}} <: Functor{C,D}
    # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
    #Functor{OppositeCat{C},OppositeCat{D}}
  func::F
end

dom(F::OppositeFunctor) = op(dom(F.func))
codom(F::OppositeFunctor) = op(codom(F.func))

do_ob_map(F::OppositeFunctor, x) = ob_map(F.func, x)
do_hom_map(F::OppositeFunctor, f) = hom_map(F.func, f)

do_compose(F::OppositeFunctor, G::OppositeFunctor) =
  OppositeFunctor(do_compose(F.func, G.func))

#= Not yet needed because the only natural transformations we currently support
#are `FinTransformationMap`, for which can just implement `op` directly.

""" Opposite natural transformation between opposite functors.

Call `op(::Transformation)` instead of directly instantiating this type.
"""
@auto_hash_equals struct OppositeTransformation{C,D,F,G,T<:Transformation{C,D,F,G}} <: Transformation{C,D,F,G}
    # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
    #Transformation{OppositeCat{C},OppositeCat{D},OppositeFunctor{C,D,G},OppositeFunctor{C,D,F}}
  trans::T
end

dom(α::OppositeTransformation) = op(codom(α.trans))
codom(α::OppositeTransformation) = op(dom(α.trans))

component(α::OppositeTransformation, x) = component(α.trans, x)

do_compose(α::OppositeTransformation, β::OppositeTransformation) =
  OppositeTransformation(do_compose(β.trans, α.trans))
do_composeH(α::OppositeTransformation, β::OppositeTransformation) =
  OppositeTransformation(do_composeH(α.trans, β.trans))
do_composeH(F::OppositeFunctor, β::OppositeTransformation) =
  OppositeTransformation(do_composeH(F.func, β.trans))
do_composeH(α::OppositeTransformation, H::OppositeFunctor) =
  OppositeTransformation(do_composeH(α.trans, H.func))
=#

""" Oppositization 2-functor.

The oppositization endo-2-functor on Cat, sending a category to its opposite, is
covariant on objects and morphisms and contravariant on 2-morphisms, i.e., is a
2-functor ``op: Catᶜᵒ → Cat``. For more explanation, see the
[nLab](https://ncatlab.org/nlab/show/opposite+category).
"""
op(C::Cat) = OppositeCat(C)
op(F::Functor) = OppositeFunctor(F)
#op(α::Transformation) = OppositeTransformation(α)
op(C::OppositeCat) = C.cat
op(F::OppositeFunctor) = F.func
#op(α::OppositeTransformation) = α.trans

""" 2-cell dual of a 2-category.
"""
function co end

end

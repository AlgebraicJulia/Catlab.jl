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
export Cat, TypeCat, Ob, Functor, Transformation,
  dom, codom, compose, id, ob, hom, is_hom_equal,
  ob_map, hom_map, dom_ob, codom_ob, component

using AutoHashEquals

using ...GAT, ..Sets
import ...Theories: Category2, Ob, ob, hom, dom, codom, compose, ⋅, ∘, id,
  composeH, *

# Categories
############

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
abstract type Cat{Ob,Hom} end

""" Coerce or look up object in category.
"""
ob(::Cat, x) = x

""" Coerce or look up morphism in category.
"""
hom(::Cat, f) = f

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
struct TypeCat{Ob,Hom} <: Cat{Ob,Hom} end

TypeCat(Ob::Type, Hom::Type) = TypeCat{Ob,Hom}()

Ob(::TypeCat{T}) where T = TypeSet{T}()

# FIXME: This isn't practical because types are often too tight.
#ob(::TypeCat{Ob,Hom}, x) where {Ob,Hom} = convert(Ob, x)
#hom(::TypeCat{Ob,Hom}, f) where {Ob,Hom} = convert(Hom, f)

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

""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
function Ob end

@auto_hash_equals struct IdentityFunctor{Dom<:Cat} <: Functor{Dom,Dom}
  dom::Dom
end

codom(F::IdentityFunctor) = F.dom

do_ob_map(F::IdentityFunctor, x) = ob(F.dom, x)
do_hom_map(F::IdentityFunctor, f) = hom(F.dom, f)

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
abstract type Transformation{C<:Cat,D<:Cat,Dom<:Functor{C,D},Codom<:Functor{C,D}} end

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

const IdIdTransformation{C<:Cat} = IdentityTransformation{C,C,IdentityFunctor{C}}

# 2-category of categories
##########################

@instance Category2{Cat,Functor,Transformation} begin
  dom(F::Functor) = F.dom
  codom(F::Functor) = F.codom
  id(C::Cat) = IdentityFunctor(C)

  function compose(F::Functor, G::Functor)
    codom(F) == dom(G) || error("Domain mismatch in composition $F ⋅ $G")
    compose_id(F, G)
  end

  dom(α::Transformation) = α.dom
  codom(α::Transformation) = α.codom
  id(F::Functor) = IdentityTransformation(F)

  function compose(α::Transformation, β::Transformation)
    codom(α) == dom(β) || error("Domain mismatch in composition $α ⋅ $β")
    compose_id(α, β)
  end
  function composeH(α::Transformation, β::Transformation)
    codom_ob(α) == dom_ob(β) || error("Domain mismatch in composition $α * $β")
    composeH_id(α, β)
  end
  function composeH(α::Transformation, H::Functor)
    codom_ob(α) == dom(H) || error("Domain mismatch in whiskering $α * $H")
    composeH_id(α, H)
  end
  function composeH(F::Functor, β::Transformation)
    codom(F) == dom_ob(β) || error("Domain mismatch in whiskering $F * $β")
    composeH_id(F, β)
  end
end

# XXX: Is this normalization of identities using multiple dispatch a good idea?
# In contrast to `Sets`, it requires a lot of boilerplate here.

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

function do_compose end

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

end

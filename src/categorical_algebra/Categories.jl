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
export Cat, TypeCat, Ob, Functor, dom, codom, compose, id, ob_map, hom_map

using ..Sets
import ...Theories: Ob, dom, codom, compose, id

# Generic interface
###################

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

""" Abstract base type for a functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Cat`](@ref)), so when writing generic
code one should prefer the `ob_map` and `hom_map` functions.
"""
abstract type Functor{Dom<:Cat,Codom<:Cat} end

dom(F::Functor) = F.dom
codom(F::Functor) = F.codom

""" Evaluate functor on object.
"""
function ob_map end

""" Evaluate functor on morphism.
"""
function hom_map end

""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
function Ob end

# Instances
###########

""" Pair of Julia types regarded as a category.

The Julia types should form an `@instance` of the theory of categories
([`Catlab.Theories.Category`](@ref)).
"""
struct TypeCat{Ob,Hom} <: Cat{Ob,Hom} end

Ob(::TypeCat{T}) where T = TypeSet{T}()

end

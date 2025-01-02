module CatOfCat 

export CatC, FinCatC

using StructEquality

using GATlab

using ....Theories: @default_model, dom, codom, id, compose
using ....BasicSets: AbsSet, SetOb
using ..Categories: Category, Cat, ThCategoryExplicitSets
using ..Functors: Functor, ThFunctor
using ..CompFunctor: CompositeFunctor
using ..FinCats: FinCat
using ..CompFinFunctor: CompositeFinDomFunctor
using ..FinFunctors: FinFunctor, FinDomFunctor

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
@struct_hash_equal struct CatC end

@instance ThCategoryExplicitSets{Category, Functor, AbsSet} [model::CatC] begin

  dom(f::Functor)::Category = ThFunctor.dom[getvalue(f)]()

  codom(f::Functor)::Category = ThFunctor.codom[getvalue(f)]()

  id(c::Category) = Functor(c)

  compose(f::Functor, g::Functor) = Functor(CompositeFunctor(f,g))

  ob_set()::SetOb = SetOb(Category)

  hom_set()::SetOb = SetOb(Functor)

end

@default_model ThCategory{Category, Functor} [model::CatC]

@struct_hash_equal struct FinCatC end

@instance ThCategory{FinCat, FinFunctor} [model::FinCatC] begin

  dom(f::FinFunctor)::FinCat = dom[getvalue(f)]()

  codom(f::FinFunctor)::FinCat = codom[getvalue(f)]()

  id(c::FinCat) = FinFunctor(c)

  compose(f::FinFunctor, g::FinFunctor) = FinFunctor(CompositeFinDomFunctor(f,g))

end

end # module

module CatOfCat 

export CatC, FinCatC

using StructEquality

using GATlab

using ....Theories: @default_model, dom, codom, id, compose
using ....BasicSets: SetOb
using ...Cats

""" 2-category of categories, functors, and natural transformations.

Categories in mathematics appear in the large, often as categories of sets with
extra structure, and in the small, as algebraic structures that generalize
groups, monoids, preorders, and graphs. This division manifests in Catlab as
well. Large categories (in spirit, if not in the [technical
sense](https://ncatlab.org/nlab/show/large+category)) occur throughout Catlab as
`@instance`s of the theory of categories. For computational reasons, small
categories are usually presented by generators and relations.
"""
@struct_hash_equal struct CatC end

@instance ThCategoryExplicitSets{AbsCat, AbsFunctor} [model::CatC] begin

  dom(f::AbsFunctor)::AbsCat = ThFunctor.dom[getvalue(f)]()

  codom(f::AbsFunctor)::AbsCat = ThFunctor.codom[getvalue(f)]()

  id(c::AbsCat) = Functor(c)

  # this will create either a CompositeFunctor or a CompositeFinDomFunctor
  # depending on whether dom(f) is FinCat or not
  compose(f::AbsFunctor, g::AbsFunctor) = compose_abs_functor(f,g)

  ob_set()::SetOb = SetOb(AbsCat)

  hom_set()::SetOb = SetOb(AbsFunctor)

end

@default_model ThCategory{AbsCat, AbsFunctor} [model::CatC]

"""
Subcategory of Cat which has only finitely-presented categories and functors 
between them.
"""
@struct_hash_equal struct FinCatC end

@instance ThCategory{FinCat, FinFunctor} [model::FinCatC] begin

  dom(f::FinFunctor)::FinCat = dom[getvalue(f)]()

  codom(f::FinFunctor)::FinCat = codom[getvalue(f)]()

  id(c::FinCat)::FinFunctor = FinFunctor(c)

  compose(f::FinFunctor, g::FinFunctor)::FinFunctor = 
    FinFunctor(CompositeFinDomFunctor(f,g)) |> validate

end

end # module

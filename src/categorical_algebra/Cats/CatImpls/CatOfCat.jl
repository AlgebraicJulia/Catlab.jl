module CatOfCat 

export CatC, FinCatC

using StructEquality

using GATlab

using ....Theories: @default_model, dom, codom, id, compose
using ..Categories: Category
using ..Functors: Functor, CompositeFunctor, ThFunctor


""" Category of Categories """
@struct_hash_equal struct CatC <: Model{Tuple{Category, Functor}} end

@instance ThCategory{Category, Functor} [model::CatC] begin

  dom(f::Functor)::Category = ThFunctor.dom[getvalue(f)]()

  codom(f::Functor)::Category = ThFunctor.codom[getvalue(f)]()

  id(c::Category) = Functor(c)

  compose(f::Functor, g::Functor) = Functor(CompositeFunctor(f,g))

end

@default_model ThCategory{Category, Functor} [model::CatC]

end # module

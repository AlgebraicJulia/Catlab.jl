module TypeCats 
export TypeCat 

using GATlab

using .....BasicSets: SetOb
using ..Categories: ThCategoryExplicitSets, ThCategory

using .ThCategory

"""
A TypeCat is just a wrapper around a model of `ThCategory`. The objects are the 
values of the Julia type parameter, `Ob`, and the morphisms are the values of 
the Julia type parameter, `Hom`.

"""
ThCategory.Meta.@typed_wrapper TypeCat

# ThCategoryExplicitSets Implementation
######################################

@instance ThCategoryExplicitSets{Ob,Hom
                                } [model::TypeCat{Ob,Hom}] where {Ob,Hom} begin

  dom(f::Hom) = dom(model, f)

  codom(f::Hom) = codom(model, f)

  id(x::Ob) = id(model, x)

  compose(f::Hom,g::Hom) = compose(model, f, g)

  ob_set() = SetOb(Ob) # creates a TypeSet

  hom_set() = SetOb(Hom) # creates a TypeSet

end

end # module

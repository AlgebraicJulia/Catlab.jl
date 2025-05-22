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

Base.show(io::IO, ::TypeCat{Ob,Hom}) where {Ob,Hom} = 
  print(io, "TypeCat($Ob,$Hom)")

# ThCategoryExplicitSets Implementation
######################################

@instance ThCategoryExplicitSets{Ob,Hom
                                } [model::TypeCat{Ob,Hom}] where {Ob,Hom} begin

  dom(f::Hom) = dom(WithModel(getvalue(model)), f)

  codom(f::Hom) = codom(WithModel(getvalue(model)), f)

  id(x::Ob) = id(model, x)

  compose(f::Hom,g::Hom) = compose(model, f, g)

  ob_set() = SetOb(Ob) # creates a TypeSet

  hom_set() = SetOb(Hom) # creates a TypeSet

end

end # module

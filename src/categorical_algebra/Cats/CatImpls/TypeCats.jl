module TypeCats 
export TypeCat 

using StructEquality

using GATlab

using ....BasicSets: SetOb, AbsSet
using ..Categories: CatImpl, ThCategoryExplicitSets

"""
A TypeCat is just a wrapper around a model of `ThCategory`. The objects are the 
values of the Julia type parameter, `Ob`, and the morphisms are the values of 
the Julia type parameter, `Hom`.

"""
@struct_hash_equal struct TypeCat{Ob,Hom} <: CatImpl{Ob,Hom}
  m::Model{Tuple{Ob,Hom}}
  function TypeCat(m::Model{Tuple{Ob,Hom}}) where {Ob,Hom}
    implements(m, ThCategory) ? new{Ob,Hom}(m) : error("Bad model")
  end 
end

# Accessor 
##########

getvalue(c::TypeCat) = c.m

# ThCategoryExplicitSets Implementation
######################################

@instance ThCategoryExplicitSets{Ob,Hom,AbsSet} [model::TypeCat{Ob,Hom}
                                                ] where {Ob,Hom} begin

  dom(f::Hom) = ThCategory.dom[getvalue(model)](f)

  codom(f::Hom) = ThCategory.codom[getvalue(model)](f)

  id(x::Ob) = ThCategory.id[getvalue(model)](x)

  compose(f::Hom,g::Hom) = ThCategory.compose[getvalue(model)](f, g)

  ob_set() = SetOb(Ob)

  hom_set() = SetOb(Hom)

end

# Category(m::Model{Tuple{Ob,Hom}}) where {Ob, Hom} = Category(TypeCat(m))

end # module


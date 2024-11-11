module OpCats 
export OpCat, op

using StructEquality

using GATlab
import GATlab: op, getvalue

using ....BasicSets: AbsSet
using ..Categories: CatImpl, ThCategoryExplicitSets, Category, ob_set, hom_set,
                    dom, codom

""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeCat{Ob,Hom} <: CatImpl{Ob,Hom}
  cat::Category
  function OppositeCat(c::Category)
    T = supertype(typeof(getvalue(c)))
    O,H = T.parameters[1].parameters
    new{O,H}(c)
  end
end

# Accessor 
##########

getvalue(c::OppositeCat) = c.cat

# ThCategoryExplicitSets Implementation
#######################################

@instance ThCategoryExplicitSets{Ob,Hom,AbsSet} [model::OppositeCat{Ob,Hom}
                                                ] where {Ob,Hom} begin
  dom(f::Hom) = codom(getvalue(model), f)

  codom(f::Hom) = dom(getvalue(model), f)

  id(x::Ob) = id(getvalue(model), x)

  compose(f::Hom,g::Hom) = compose(getvalue(model), g, f)

  ob_set() = ob_set(getvalue(model))

  hom_set() = hom_set(getvalue(model))

end

# Constructor
#############

op(c::Category) = Category(OppositeCat(c))


end # module

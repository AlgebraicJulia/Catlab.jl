module OpCats 
export OpCat, op

using StructEquality

using GATlab

using .....BasicSets, ..Categories

""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeCat{Ob,Hom}
  cat::Category
  function OppositeCat(c::Category)
    new{impl_type(c, :Ob), impl_type(c, :Hom)}(c)
  end
end

# Accessor 
##########

GATlab.getvalue(c::OppositeCat) = c.cat

# ThCategoryExplicitSets Implementation
#######################################

@instance ThCategoryExplicitSets{Ob,Hom} [model::OppositeCat{Ob,Hom}
                                                ] where {Ob,Hom} begin
  dom(f::Hom) = codom(getvalue(model), f)

  codom(f::Hom) = dom(getvalue(model), f)

  id(x::Ob) = id(getvalue(model), x)

  compose(f::Hom,g::Hom) = compose(getvalue(model), g, f)

  ob_set()::SetOb = ob_set(getvalue(model))

  hom_set()::SetOb = hom_set(getvalue(model))

end

# Constructor
#############

op(c::Category) = Category(OppositeCat(c))

end # module

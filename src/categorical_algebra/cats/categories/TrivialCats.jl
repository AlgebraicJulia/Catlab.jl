module TrivialCats 
export TrivialCat

using StructEquality

using GATlab

using .....BasicSets: AbsSet, SingletonSet, SetOb
using ..Categories: ThCategoryExplicitSets, Category
import ..Categories: Category

""" 
Terminal category in the category of categories: one object, one id morphism.
"""
@struct_hash_equal struct TrivialCat end

# ThCategoryExplicitSets Implementation
#######################################

@instance ThCategoryExplicitSets{Nothing,Nothing} [model::TrivialCat]  begin
  dom(::Nothing) = nothing

  codom(::Nothing) = nothing

  id(::Nothing) = nothing

  compose(::Nothing,::Nothing) = nothing

  ob_set() = SetOb(SingletonSet())

  hom_set() = SetOb(SingletonSet())

end

# Constructor
#############

Category(::Nothing) = Category(TrivialCat())

end # module

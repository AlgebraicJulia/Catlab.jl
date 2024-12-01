module TrivialCats 
export TrivialCat

using StructEquality

using GATlab

using .....BasicSets: AbsSet, SingletonSet
using ..Categories: CatImpl, ThCategoryExplicitSets, Category
import ..Categories: Category

""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@struct_hash_equal struct TrivialCat <: CatImpl{Nothing,Nothing}
end

# ThCategoryExplicitSets Implementation
#######################################

@instance ThCategoryExplicitSets{Nothing,Nothing,AbsSet} [model::TrivialCat]   begin
  dom(f::Nothing) = nothing

  codom(f::Nothing) = nothing

  id(x::Nothing) = nothing

  compose(f::Nothing,g::Nothing) = nothing

  ob_set() = SetOb(SingletonSet())

  hom_set() = SetOb(SingletonSet())

end

# Constructor
#############

Category(::Nothing) = Category(TrivialCat())

end # module

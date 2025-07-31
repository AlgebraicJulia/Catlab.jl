module TrivialCats 
export TrivialCat

using StructEquality

using GATlab

using .....BasicSets: SingletonSet, SetOb, FinSet, EmptySet, AbstractFunction
using ..Categories: ThCategoryExplicitSets, ThCategoryWithMonicsEpics, ThConcreteCategory, Category
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

  ob_set()::SetOb = SetOb(SingletonSet())

  hom_set()::SetOb = SetOb(SingletonSet())

end

@instance ThCategoryWithMonicsEpics{Nothing,Nothing} [model::TrivialCat]  begin
  is_monic(::Nothing) = true
  is_epic(::Nothing) = true
end

@instance ThConcreteCategory{Nothing,Nothing} [model::TrivialCat]  begin

  ob_map(::Nothing) = FinSet(EmptySet()) 
  hom_map(::Nothing) = FinFunction(EmptySet())
  lift(::AbstractFunction, ::Nothing, ::Nothing) = nothing

end

# Constructor
#############

Category(::Nothing) = Category(TrivialCat())

end # module

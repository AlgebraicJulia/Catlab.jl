module TestCategories
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.Sets, Catlab.CategoricalAlgebra.Categories

# Categories from Julia types
#############################

C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
@test Ob(C) == TypeSet(FreeCategory.Ob)

end

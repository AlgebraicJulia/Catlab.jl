module TestCategories
using Test

using Catlab.Theories, Catlab.BasicSets
using Catlab.CategoricalAlgebra

# Instances
###########

# Categories
#-----------

C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
@test sprint(show, C) == "TypeCat($(FreeCategory.Ob), $(FreeCategory.Hom))"

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)
@test ob(C, x) == x
@test hom(C, f) == f

end

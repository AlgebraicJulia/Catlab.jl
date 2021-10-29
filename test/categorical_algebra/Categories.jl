module TestCategories
using Test

using Catlab.Theories
using Catlab.CategoricalAlgebra.Sets, Catlab.CategoricalAlgebra.Categories

# Categories from Julia types
#############################

C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
@test Ob(C) == TypeSet(FreeCategory.Ob)
@test sprint(show, C) == "TypeCat($(FreeCategory.Ob), $(FreeCategory.Hom))"

F = id(C)
@test (dom(F), codom(F)) == (C, C)
@test startswith(sprint(show, F), "id(TypeCat(")

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)
@test F(x) == x
@test F(f) == f

α = id(F)
@test (dom(α), codom(α)) == (F, F)

end

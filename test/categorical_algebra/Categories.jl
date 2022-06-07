module TestCategories
using Test

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra.Sets, Catlab.CategoricalAlgebra.Categories

# Instances
###########

# Categories
#-----------

C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
@test Ob(C) == TypeSet(FreeCategory.Ob)
@test sprint(show, C) == "TypeCat($(FreeCategory.Ob), $(FreeCategory.Hom))"

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)
@test ob(C, x) == x
@test hom(C, f) == f

# Functors
#---------

F = id(C)
@test (dom(F), codom(F)) == (C, C)
@test startswith(sprint(show, F), "id(TypeCat(")
@test F(x) == x
@test F(f) == f

function InstanceFunctor(T::TypeCat{Ob,Hom}) where {Ob, Hom}
  Functor(x -> functor((Ob,Hom), x), f -> functor((Ob,Hom), f),
          TypeCat{FreeCategory.Ob, FreeCategory.Hom}(), T)
end
F = InstanceFunctor(TypeCat(FreeCategory2.Ob, FreeCategory2.Hom))
@test dom(F) == C

x′, y′ = Ob(FreeCategory2, :x, :y)
f′ = Hom(:f, x′, y′)
@test F(x) == x′
@test F(f) == f′

F_op = op(F)
@test F_op isa Categories.OppositeFunctor
@test (dom(F_op), codom(F_op)) == (op(dom(F)), op(codom(F)))
@test F_op(x) == x′
@test F_op(f) == f′

# Transformations
#----------------

α = id(F)
@test (dom(α), codom(α)) == (F, F)
@test component(α, x) == id(F(x))

end

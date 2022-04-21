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

# Functors
#---------

F = id(C)
@test (dom(F), codom(F)) == (C, C)
@test startswith(sprint(show, F), "id(TypeCat(")

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)
@test F(x) == x
@test F(f) == f

# Is this worth putting somewhere?
struct InstanceFunctor{Ob,Hom} <:
  Functor{TypeCat{FreeCategory.Ob,FreeCategory.Hom},TypeCat{Ob,Hom}}
end
Categories.dom(::InstanceFunctor) = TypeCat{FreeCategory.Ob,FreeCategory.Hom}()
Categories.codom(::InstanceFunctor{Ob,Hom}) where {Ob,Hom} = TypeCat{Ob,Hom}()
Categories.do_ob_map(::InstanceFunctor{Ob,Hom}, x) where {Ob,Hom} =
  functor((Ob,Hom), x)::Ob
Categories.do_hom_map(::InstanceFunctor{Ob,Hom}, f) where {Ob,Hom} =
  functor((Ob,Hom), f)::Hom

F = InstanceFunctor{FreeCategory2.Ob,FreeCategory2.Hom}()

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

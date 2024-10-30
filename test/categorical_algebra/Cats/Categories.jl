module TestCategories

using Test, Catlab, GATlab

# Instances
###########

# Categories
#-----------
M = FreeCategory.Meta.M();
C = Category(M)
@test getvalue(C) isa TypeCat{FreeCategory.Ob, FreeCategory.Hom}
@test Ob(C) == SetOb(FreeCategory.Ob)
@test C isa Category{FreeCategory.Ob, FreeCategory.Hom}

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)

Co = op(C)
@test codom(C, f) == dom(Co, f) == codom(f) == y

# Functors
#---------
const Ct = CatC()
using Catlab.CategoricalAlgebra.Cats.Categories: IdentityFunctor
i = IdentityFunctor(C)
F = id(C);


@test (dom(F), codom(F)) == (C, C)
# @test startswith(sprint(show, F), "id(TypeCat(")
@test F(x) == x
@test F(f) == f

function InstanceFunctor(T::Category{Ob,Hom}) where {Ob, Hom}
  Functor(x -> functor((Ob,Hom), x), f -> functor((Ob,Hom), f), C, T)
end

Map = @theorymap Incl(ThCategory,ThCategory2) begin 
  Ob => Ob 
  Hom(x,y) ⊣ [x::Ob, y::Ob] => Hom(x,y)
  id(x) ⊣ [x::Ob] => id(x)
  compose(f,g) ⊣ [(x,y,z)::Ob, f::Hom(x,y), g::Hom(y,z)] => compose(f,g)
end

MM = Category(migrate_model(Map, FreeCategory2.Meta.M()))

@test MM isa Category{FreeCategory2.Ob, FreeCategory2.Hom}


F = InstanceFunctor(MM)
@test dom(F) == C

x′, y′ = Ob(FreeCategory2, :x, :y)
f′ = Hom(:f, x′, y′)
@test F(x) == x′
@test F(f) == f′

id(MM, x′)


F_op = op(F)
@test getvalue(F_op) isa Categories.OppositeFunctor
@test (dom(F_op), codom(F_op)) == (op(dom(F)), op(codom(F)))
@test F_op(x) == x′
@test F_op(f) == f′

# Transformations
#----------------

α = id[Cat2()](F)

@test (dom[Cat2()](α), codom[Cat2()](α)) == (F, F)

@test component(α, x) == id(F(x))

end

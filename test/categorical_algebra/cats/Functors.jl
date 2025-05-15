module TestFunctors 

using Catlab, Test

# Functors
#---------
C = Category(TypeCat(FreeCategory.Meta.M);)
x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)

F = Functor(C)
@test getvalue(F) isa IdentityFunctor

@test (dom(F), codom(F)) == (C, C)
@test startswith(sprint(show, F), "id(TypeCat(")
@test ob_map(F,x) == x
@test hom_map(F,f) == f

function InstanceFunctor(T::Category)
  Ob, Hom = obtype(T), homtype(T)
  Functor(x -> functor((Ob,Hom), x), f -> functor((Ob,Hom), f), C, T)
end

Map = @theorymap Incl(ThCategory,ThCategory2) begin 
  Ob => Ob 
  Hom(x,y) ⊣ [x::Ob, y::Ob] => Hom(x,y)
  id(x) ⊣ [x::Ob] => id(x)
  compose(f,g) ⊣ [(x,y,z)::Ob, f::Hom(x,y), g::Hom(y,z)] => compose(f,g)
end

MM = Category(TypeCat(migrate_model(Map, FreeCategory2.Meta.M)))

@test obtype(MM) == FreeCategory2.Ob
@test homtype(MM) == FreeCategory2.Hom

F = InstanceFunctor(MM)
@test dom(F) == C

x′, y′ = Ob(FreeCategory2, :x, :y)
f′ = Hom(:f, x′, y′)
@test ob_map(F,x) == x′
@test hom_map(F,f) == f′

@test id(MM, x′) isa FreeCategory2.Hom

F_op = op(F)
@test getvalue(F_op) isa Cats.OppositeFunctor
@test (dom(F_op), codom(F_op)) == (op(dom(F)), op(codom(F)))
@test ob_map(F_op,x) == x′
@test hom_map(F_op,f) == f′

end # module
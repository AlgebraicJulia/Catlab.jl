module TestTransformations 

using Catlab, Test

function InstanceFunctor(T::TypeCat{Ob,Hom}) where {Ob, Hom}
  Functor(x -> functor((Ob,Hom), x), f -> functor((Ob,Hom), f),
          TypeCat{FreeCategory.Ob, FreeCategory.Hom}(), T)
end


C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
x, y = Ob(FreeCategory, :x, :y)
F = InstanceFunctor(TypeCat(FreeCategory2.Ob, FreeCategory2.Hom))

α = id(F)
@test (dom(α), codom(α)) == (F, F)
@test component(α, x) == id(F(x))

# Commutative square as natural transformation.
C = FinCat(path_graph(Graph, 2))
F = FinDomFunctor([FinSet(4), FinSet(2)], [FinFunction([1,1,2,2])], C)
α₀, α₁ = FinFunction([3,4,1,2]), FinFunction([2,1])
α = FinTransformation([α₀, α₁], F, F)
@test is_natural(α)
@test (α[1], α[2]) == (α₀, α₁)
@test components(α) == [α₀, α₁]
@test α⋅α == FinTransformation([FinFunction(1:4), FinFunction(1:2)], F, F)

end # module

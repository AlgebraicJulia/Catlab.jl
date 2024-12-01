module TestSubsets 

using Test, Catlab
using Catlab.CategoricalAlgebra.Subsets: predicate


X = FinSet(10)
A, B = SubFinSet(X, [1,2,5,6,8,9]), SubFinSet(X, [2,3,5,7,8])
@test ob(A) == X
A_pred = SubFinSet(Bool[1,1,0,0,1,1,0,1,1,0])
@test hom(A) == hom(A_pred)
@test predicate(A) == predicate(A_pred)

# Lattice of subsets.
@test A ∧ B |> force == SubFinSet(X, [2,5,8])
@test A ∨ B |> force == SubFinSet(X, [1,2,3,5,6,7,8,9])

@test ⊤(X) |> collect == SubFinSet(X, 1:10) |> collect
@test ⊥(X) |> collect == SubFinSet(X, 1:0) |> collect

collect_eq(x,y) = sort(collect(x)) == sort(collect(y))

const C = Category(TypeCat(SetC()))

for alg in (SubOpBoolean(), SubOpWithLimits())
  @test collect_eq(meet(A, B, C, alg), SubFinSet(X, [2,5,8]))
  @test collect_eq(join(A, B, C, alg), SubFinSet(X, [1,2,3,5,6,7,8,9]))
  @test collect_eq(top(X, C, alg),     SubFinSet(X, 1:10))
  @test collect_eq(bottom(X, C, alg),  SubFinSet(X, 1:0))
end

end # module

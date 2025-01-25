
# Subsets
#########

X = FinSet(10)
A, B = SubFinSet(X, [1,2,5,6,8,9]), SubFinSet(X, [2,3,5,7,8])
@test ob(A) == X
A_pred = SubFinSet(Bool[1,1,0,0,1,1,0,1,1,0])
@test hom(A) == hom(A_pred)
@test FinSetCats.predicate(A) == FinSetCats.predicate(A_pred)

# Lattice of subsets.
@test A ∧ B |> force == SubFinSet(X, [2,5,8])
@test A ∨ B |> force == SubFinSet(X, [1,2,3,5,6,7,8,9])
@test ⊤(X) |> force == SubFinSet(X, 1:10)
@test ⊥(X) |> force == SubFinSet(X, 1:0)

for alg in (SubOpBoolean(), SubOpWithLimits())
  @test meet(A, B, alg) |> sort == SubFinSet(X, [2,5,8])
  @test join(A, B, alg) |> sort == SubFinSet(X, [1,2,3,5,6,7,8,9])
  @test top(X, alg) |> force == SubFinSet(X, 1:10)
  @test bottom(X, alg) |> force == SubFinSet(X, 1:0)
end
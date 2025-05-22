module TestSubsets 

using Test, Catlab

X = FinSet(10)
A, B = SubFinSet(X, [1,2,5,6,8,9]), SubFinSet(X, [2,3,5,7,8])

@test ob(A) == X
A_pred = SubFinSet(Bool[1,1,0,0,1,1,0,1,1,0])
@test hom(A) == hom(A_pred)
@test predicate(A) == predicate(A_pred)

# Lattice of subsets.
@withmodel SubobjectElementWise()  (∧, ∨, ⊤, ⊥) begin 
  @test A ∧ B |> force == SubFinSet(X, [2,5,8])
  @test A ∨ B |> force == SubFinSet(X, [1,2,3,5,6,7,8,9])

  @test ⊤(X) |> collect == SubFinSet(X, 1:10) |> collect
  @test ⊥(X) |> collect == SubFinSet(X, 1:0) |> collect
end

collect_eq(x,y) = sort(collect(x)) == sort(collect(y))

for m in [SubobjectElementWise(), SubOpCatLimits(FinSetC())]
  @test collect_eq(meet[m](A, B), SubFinSet(X, [2,5,8]))
  @test collect_eq(join[m](A, B), SubFinSet(X, [1,2,3,5,6,7,8,9]))
  @test collect_eq(top[m](X),     SubFinSet(X, 1:10))
  @test collect_eq(bottom[m](X),  SubFinSet(X, 1:0))
end 

end # module

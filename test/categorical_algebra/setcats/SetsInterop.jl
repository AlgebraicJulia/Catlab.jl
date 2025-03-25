module TestSetsInterop 

using Catlab, Test 

C = TypeCat(FreeCategory.Ob, FreeCategory.Hom)
@test Ob(C) == TypeSet(FreeCategory.Ob)

C = FinCat(parallel_arrows(Graph, 3))
@test Ob(C) == FinSet(2)

end # module
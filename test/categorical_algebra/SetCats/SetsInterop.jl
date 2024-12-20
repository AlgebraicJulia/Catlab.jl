

C = Category(TypeCat(FreeCategory.Meta.M))
@test U_CatSet(C) == SetOb(FreeCategory.Ob)


C = FinCat(parallel_arrows(Graph, 3))
@test U_CatSet(C) == FinSet(2) # Replaced "Ob"

C = FinCat(parallel_arrows(Graph, 2))
F = FinDomFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
@test U_CatSet(F) == FinFunction([1,4], FinSet(4))

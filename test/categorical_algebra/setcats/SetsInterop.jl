module TestSetsInterop

using Catlab, Test

C = Category(TypeCat(FreeCategory.Meta.M))
@test ob_map(U_CatSet, C) == SetOb(FreeCategory.Ob)


C = FinCat(parallel_arrows(Graph, 3))
@test ob_map(U_CatSet,C) == SetOb(FinSetInt(2)) # Replaced "Ob"

C = FinCat(parallel_arrows(Graph, 2))
D = FinCat(@acset Graph begin V=4; E=4; src=[1,1,2,3]; tgt=[2,3,4,4] end)

F = FinDomFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D; homtype=:list)
@test hom_map(U_CatSet, F) == FinDomFunction([1,4], SetOb(FinSetInt(4)))

end # module

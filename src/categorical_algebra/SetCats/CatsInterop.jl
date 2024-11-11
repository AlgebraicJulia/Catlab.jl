module CatsInterop 
export U_CatSet

using ...Cats.Categories: Cat, ob_set
using ...Cats.FinCats: FinCat

using ...BasicSets.Sets: SetOb
using ...Cats.FinFunctors: FinDomFunctor, collect_ob

""" Forgetful functor Cat → Set.

Sends a category to its set of objects and a functor to its object map. This was formerly called `Ob`
"""
U_CatSet(c::Cat) = ob_set(c)

U_CatSet(c::FinCat) = ob_set(c)


""" Forgetful functor Cat to Set """
U_CatSet(F::FinDomFunctor) = FinDomFunction(collect_ob(F), U_CatSet(codom(F)))


end # module

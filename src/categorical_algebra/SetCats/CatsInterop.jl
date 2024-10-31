module CatsInterop 

import ....Theories: Ob
using ...Cats.Categories: Cat
using ...BasicSets.Sets: SetOb
using ...Cats.FinFunctors: FinFunctor, collect_ob

""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
Ob(::Cat{O,H}) where {O,H} = SetOb(O)


""" Forgetful functor Cat to Set """
Ob(F::FinFunctor{Int}) = FinDomFunction(collect_ob(F), Ob(codom(F)))


end # module

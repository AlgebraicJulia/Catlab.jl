module Colimits 

using StructEquality, StaticArrays, DataStructures

using GATlab

using .....Theories, .....Graphs, .....BasicSets
using ....Cats
import ....Cats: colimit,universal
using ..SetCat: SetC

##################
# Initial object #
##################

@instance ThCategoryWithInitial{SetOb,SetFunction} [model::SetC] begin 

  colimit(d::EmptyDiagram) = colimit[FinSetC()](d)
    
  universal(::AbsColimit, ::EmptyDiagram, x::Multicospan) =
    SetFunction(Dict{Union{},eltype(apex(x))}(), apex(x))
end 

##############
# Coproducts #
##############

@instance ThCategoryUnbiasedCoproducts{SetOb,SetFunction} [model::SetC] begin

  function colimit(d::DiscreteDiagram)::AbsColimit
    all(x -> x isa FinSet, d) && return colimit[FinSetC()](d)
    Xs = collect(d)
    S = SumSet(Xs) |> SetOb
    ιs = [SetFunction(CallableFunction(i->TaggedElem(i, j), X, S)) 
          for (j, X) in enumerate(Xs)]
    csp = Multicospan{SetOb, SetFunction, SetOb}(S, ιs, Xs)
    ColimitCocone(csp, FreeDiagram(d))
  end

  function universal(lim::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    fun(t::TaggedElem) = cocone[getidx(t)](getvalue(t))
    SetFunction(CallableFunction(fun, ob(lim), SetOb(apex(cocone))))
  end
end

end # module

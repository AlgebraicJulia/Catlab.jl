module FinSetCatColimits 

using StructEquality, StaticArrays, DataStructures

using GATlab

using .....Theories, .....Graphs, .....BasicSets
using ....Cats
using ..FinSetCat: FinSetC

##################
# Initial object #
##################

@instance ThCategoryWithInitial{FinSet,FinFunction} [model::FinSetC] begin 

  colimit(::EmptyDiagram) =
    InitialColimit{FinSet,FinFunction}(FinSet(EmptySet()))
    
  universal(::AbsColimit, ::EmptyDiagram, x::Multicospan) =
    FinFunction(eltype(apex(x))[], apex(x))
end 

##############
# Coproducts #
##############

"""
Take a coproduct where the apex has TaggedElems.
"""
@instance ThCategoryUnbiasedCoproducts{FinSet,FinFunction} [model::FinSetC] begin

  function colimit(d::DiscreteDiagram)::AbsColimit
    Xs = collect(d)
    S = SumSet(Xs) |> FinSet
    ιs = [FinFunction(i->TaggedElem(i, j), X, S) for (j, X) in enumerate(Xs)]
    csp = Multicospan{FinSet, FinFunction, FinSet}(S, ιs, Xs)
    ColimitCocone(csp, FreeDiagram(d))
  end

  function universal(lim::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    fun(t::TaggedElem) = cocone[getidx(t)](getvalue(t))
    FinFunction(fun, ob(lim), FinSet(apex(cocone)))
  end
end

################
# Coequalizers #
################

@instance ThCategoryWithCoequalizers{FinSet,FinFunction} [model::FinSetC] begin

  function colimit(para::ParallelMorphisms)::AbsColimit
    @assert !isempty(para)
    f1, frest = para[1], para[2:end]
    cod_elems = Vector{eltype(codom(para))}(collect(codom(para)))
    sets = DisjointSets(cod_elems)
    for elem in dom(para)
      for f in frest
        union!(sets, f1(elem), f(elem))
      end
    end
    q = quotient_projection(sets, codom(para))
    ColimitCocone(Multicospan([q]), FreeDiagram(para))  
  end

  function universal(res::AbsColimit,::ParallelMorphisms, x::Multicospan)
    pass_to_quotient(only(cocone(res)), only(x))
  end
end


""" Create projection map π: X → X/∼ from partition of X.
"""
function quotient_projection(sets::DisjointSets, domset::FinSet)
  h = [ find_root!(sets, i) for i in sets]
  roots = unique!(h) |> FinSet # don't assume we can sort elements
  FinFunction(Dict(x => find_root!(sets, x) for x in domset), domset, roots)
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction, h::FinFunction)
  dom(π) ≃ dom(h) || error("$(dom(π)) ≠ $(dom(h)) ")
  X, Q, Y = dom(h), codom(π), codom(h)
  q = Dict{eltype(Q), eltype(Y)}()
  for i in X
    j = π(i)
    if !haskey(q, j)
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  all(j -> haskey(q, j), Q) || error("Projection map is not surjective")
  FinFunction(q, Q, Y)
end


############
# Pushouts #
############

@instance ThCategoryWithPushouts{FinSet, FinFunction} [model::FinSetC] begin

  function colimit(spn::Multispan)
    composite_colimit(CatWithCoequalizers(model), spn)
  end
   
  
  function universal(res::AbsColimit, diag::Multispan, x::Multicospan)  
    composite_universal(CatWithCoequalizers(model), res, x)
  end

end

end # module

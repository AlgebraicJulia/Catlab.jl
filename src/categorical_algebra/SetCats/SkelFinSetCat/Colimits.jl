module Colimits 

using DataStructures

using ACSets, GATlab

using .....Theories, .....Graphs, .....BasicSets,  ....Cats
using ..SkelFinSetCat
import ....Cats: composite_universal, diagram


###########
# Initial #
###########

@instance ThCategoryWithInitial{FinSetInt,FinFunction} [model::SkelFinSet] begin 

  colimit(::EmptyDiagram)::AbsColimit = 
    InitialColimit{FinSetInt,FinFunction}(FinSetInt(0))

  universal(::AbsColimit, ::EmptyDiagram, a::Multicospan) = 
    FinFunction(Int[], FinSet(apex[model](a)))
end

##############
# Coproducts #
##############

@instance ThCategoryUnbiasedCoproducts{FinSetInt,FinFunction} [model::SkelFinSet] begin

  function colimit(Xs::DiscreteDiagram)::AbsColimit
    ns = length.(Xs)
    n = sum(ns)
    offsets = [0,cumsum(ns)...]
    ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
    csp = Multicospan{FinSetInt, FinFunction, FinSetInt}(
      FinSetInt(n), ιs, FinSetInt.(ns)
    )
    ColimitCocone(csp, FreeDiagram(Xs))
  end

  function universal(::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    v = mapreduce(collect, vcat, cocone, init=Int[])
    FinFunction(v, FinSet(apex(cocone)))  
  end
end

################
# Coequalizers #
################

@instance ThCategoryWithCoequalizers{FinSetInt, FinFunction} [model::SkelFinSet] begin

  function colimit(para::ParallelMorphisms)
    emp = EmptyDiagram{impl_type(model, ThCategory, :Ob)}()
    isempty(para) && return colimit(emp) 
    f1, frest = para[1], para[2:end]
    m, n = length(dom(para)), length(codom(para))
    sets = IntDisjointSets(n)
    for i in 1:m
      for f in frest
        union!(sets, f1(i), f(i))
      end
    end
    q = quotient_projection(sets)
    ColimitCocone(Multicospan(codom[model](q), [q]; cat=model), FreeDiagram(para))
  end 
  
  function universal(res::AbsColimit, ::ParallelMorphisms, x::Multicospan)
    pass_to_quotient(only(cocone(res)), only(x))
  end 
end

function quotient_projection(sets::IntDisjointSets)
  h = [ find_root!(sets, i) for i in 1:length(sets) ]
  roots = unique!(sort(h))
  FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction, h::FinFunction)
  @assert dom(π) == dom(h)
  q = zeros(Int, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(==(0), q) && error("Projection map is not surjective")
  FinFunction(q, codom(h))
end

function pass_to_quotient(π::FinFunction, h::FinDomFunction)
  @assert dom(π) == dom(h)
  q = Vector{Union{Some{eltype(codom(h))},Nothing}}(nothing, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if isnothing(q[j])
      q[j] = Some(h(i))
    else
      something(q[j]) == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(isnothing, q) && error("Projection map is not surjective")
  FinDomFunction(map(something, q), codom(h))
end

############
# Pushouts #
############

@instance ThCategoryWithPushouts{FinSetInt, FinFunction} [model::SkelFinSet] begin

  colimit(spn::Multispan) =
    composite_colimit(CatWithCoequalizers(model), spn)
   
  
  function universal(res::AbsColimit, diag::Multispan, x::Multicospan)  
    composite_universal(CatWithCoequalizers(model), res, x)
  end

end


#############
# Bipartite #
#############



""" Colimit of general diagram of FinSets computed by coproduct-then-quotient.

See `Limits.CompositePushout` for a very similar construction.
"""
struct FinSetCompositeColimit<: AbsColimit
  diagram::FreeDiagram
  cocone::Multicospan
  coprod::AbsColimit
  proj::FinFunction # Projection for the "multi-coequalizer" in general formula.
end

diagram(f::FinSetCompositeColimit) = f.diagram

function composite_universal(colim::FinSetCompositeColimit, cocone::Multicospan)
  h = universal[SkelFinSet()](colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end




@instance ThCategoryWithBipartiteColimits{FinSetInt, FinFunction} [model::SkelFinSet] begin
    function colimit(d::BipartiteFreeDiagram)
      # As in a pushout, this method assume that all objects in layer 1 have
      # outgoing morphisms so that they can be excluded from the coproduct.
      @assert !any(isempty(incident(d, u, :src)) for u in vertices₁(d))
      coprod = colimit[model](DiscreteDiagram(ob₂(d)))
      n, ιs = length(ob(coprod)), legs(coprod)
      sets = IntDisjointSets(n)
      for u in vertices₁(d)
        out_edges = incident(d, u, :src)
        for (e1, e2) in zip(out_edges[1:end-1], out_edges[2:end])
          h1, h2 = hom(d, e1), hom(d, e2)
          ι1, ι2 = ιs[tgt(d, e1)], ιs[tgt(d, e2)]
          for i in ob₁(d, u)
            union!(sets, ι1(h1(i)), ι2(h2(i)))
          end
        end
      end
      π = quotient_projection(sets)
      cocone = Multicospan(codom[model](π), 
                           [compose[model](ιs[i],π) for i in vertices₂(d) ]; 
                           cat=model)
      FinSetCompositeColimit(FreeDiagram(d), cocone, coprod, π)
    end
    function universal(lim::AbsColimit, ::BipartiteFreeDiagram, c::Multicospan)
      composite_universal(lim, c)
    end

end


##############
# Free Graph #
##############

@instance ThCategoryWithColimits{FinSetInt, FinFunction} [model::SkelFinSet] begin
    function colimit(d::FreeGraph)
      # Uses the general formula for colimits in Set (Leinster, 2014, Basic Category
      # Theory, Example 5.2.16).
      coprod = coproduct[model](d[:ob]...)
      n, ιs = length(ob(coprod)), legs(coprod)
      sets = IntDisjointSets(n)
      for f in edges(d)
        s, t, h = src(d, f), tgt(d, f), d[f, :hom]
        for i in dom(h)
          union!(sets, ιs[s](i), ιs[t](h(i)))
        end
      end
      π = quotient_projection(sets)
      cocone = Multicospan(codom[model](π), 
                           map(x -> compose[model](ιs[x],π), vertices(d)); 
                           cat=model)
      FinSetCompositeColimit(FreeDiagram(d), cocone, coprod, π)
    end
    function universal(lim::AbsColimit, ::FreeGraph, c::Multicospan)
      composite_universal(lim, c)
    end

end

end # module

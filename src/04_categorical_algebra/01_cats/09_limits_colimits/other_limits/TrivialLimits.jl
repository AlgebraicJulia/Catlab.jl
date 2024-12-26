module TrivialLimits 

using GATlab

using ...Categories: TrivialCat
using ...FreeDiagrams: Multispan, Multicospan, EmptyDiagram,DiscreteDiagram, FreeDiagram
using ..LimitsColimits

@instance ThCategoryUnbiasedCoproducts{Nothing,Nothing,AbsSet,AbsColimit,Multicospan,
    EmptyDiagram, DiscreteDiagram} [model::TrivialCat] begin 

  colimit(::EmptyDiagram)::AbsColimit = InitialColimit{Nothing,Nothing}(nothing)
  universal(::AbsColimit, ::EmptyDiagram, ::Multicospan) = nothing
  colimit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end
  universal(::AbsColimit, ::DiscreteDiagram, ::Multicospan) = nothing

end

@instance ThCategoryUnbiasedProducts{Nothing,Nothing,AbsSet,AbsLimit,Multispan,
    EmptyDiagram, DiscreteDiagram} [model::TrivialCat] begin 

  limit(::EmptyDiagram)::AbsLimit = InitialColimit{Nothing,Nothing}(nothing)
  universal(::AbsLimit, ::EmptyDiagram, ::Multispan) = nothing
  limit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    LimitCone(Multispan(nothing, ns, ns), FreeDiagram(d))
  end
  universal(::AbsLimit, ::DiscreteDiagram, ::Multispan) = nothing

end



end # module

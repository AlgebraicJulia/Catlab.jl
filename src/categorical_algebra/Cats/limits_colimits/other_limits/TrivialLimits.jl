module TrivialLimits 

using GATlab

using ...Categories: TrivialCat
using ...FreeDiagrams
using ..LimitsColimits

@instance ThCategoryWithInitial{Nothing,Nothing,AbsSet,AbsColimit,Multicospan, 
                                EmptyDiagram} [model::TrivialCat] begin 

  colimit(::EmptyDiagram)::AbsColimit = InitialColimit{Nothing,Nothing}(nothing)

  universal(::AbsColimit, ::EmptyDiagram, ::Multicospan) = nothing
end

@instance ThCategoryUnbiasedCoproducts{Nothing,Nothing,AbsSet,AbsColimit, Multicospan,
                                       DiscreteDiagram} [model::TrivialCat] begin 

  colimit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::DiscreteDiagram, ::Multicospan) = nothing

end

@instance ThCategoryWithCoequalizers{Nothing,Nothing,AbsSet,AbsColimit,Multicospan,
                                     ParallelMorphisms} [model::TrivialCat] begin 

  colimit(d::ParallelMorphisms) = 
    ColimitCocone(Multicospan([nothing], [nothing], [nothing]), FreeDiagram(d))
  

  universal(::AbsColimit, ::ParallelMorphisms, ::Multicospan) = nothing
end

@instance ThCategoryWithPushouts{Nothing,Nothing,AbsSet,AbsColimit,Multicospan,
                                 Multispan} [model::TrivialCat] begin 

  colimit(d::Multispan) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::Multispan, ::Multicospan) = nothing
end


@instance ThCategoryWithTerminal{Nothing,Nothing,AbsSet,AbsLimit,Multispan,
                                 EmptyDiagram} [model::TrivialCat] begin

    limit(::EmptyDiagram)::AbsLimit = InitialColimit{Nothing,Nothing}(nothing)

    universal(::AbsLimit, ::EmptyDiagram, ::Multispan) = nothing
end

@instance ThCategoryUnbiasedProducts{Nothing,Nothing,AbsSet,AbsLimit,Multispan,
                                     DiscreteDiagram} [model::TrivialCat] begin 

  limit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    LimitCone(Multispan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsLimit, ::DiscreteDiagram, ::Multispan) = nothing
end


@instance ThCategoryWithEqualizers{Nothing,Nothing,AbsSet,AbsLimit,Multispan,
                                  ParallelMorphisms} [model::TrivialCat] begin 

  limit(d::ParallelMorphisms) = 
    LimitCone(Multispan([nothing], [nothing], [nothing]), FreeDiagram(d))

  universal(::AbsLimit, ::ParallelMorphisms, ::Multispan) = nothing
end

@instance ThCategoryWithPullbacks{Nothing,Nothing,AbsSet,AbsLimit,Multispan,
                                  Multicospan} [model::TrivialCat] begin 

  limit(d::Multicospan) = let n = length(d); ns=fill(nothing, n);
    LimitCone(Multispan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsLimit, ::Multicospan, ::Multispan) = nothing
end

end # module

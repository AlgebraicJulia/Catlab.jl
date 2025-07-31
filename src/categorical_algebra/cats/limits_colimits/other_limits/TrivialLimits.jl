module TrivialLimits 

using GATlab

using ...Categories: TrivialCat
using ...FreeDiagrams
using ..LimitsColimits

@instance ThCategoryWithInitial{Nothing,Nothing} [model::TrivialCat] begin 

  colimit(::EmptyDiagram)::AbsColimit = InitialColimit{Nothing,Nothing}(nothing)

  universal(::AbsColimit, ::EmptyDiagram, ::Multicospan) = nothing
end

@instance ThCategoryUnbiasedCoproducts{Nothing,Nothing} [model::TrivialCat] begin 

  colimit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::DiscreteDiagram, ::Multicospan) = nothing

end

@instance ThCategoryWithCoequalizers{Nothing,Nothing} [model::TrivialCat] begin 

  colimit(d::ParallelMorphisms) = 
    ColimitCocone(Multicospan([nothing], [nothing], [nothing]), FreeDiagram(d))
  

  universal(::AbsColimit, ::ParallelMorphisms, ::Multicospan) = nothing
end

@instance ThCategoryWithPushouts{Nothing,Nothing} [model::TrivialCat] begin 

  colimit(d::Multispan) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::Multispan, ::Multicospan) = nothing
end


@instance ThCategoryWithTerminal{Nothing,Nothing} [model::TrivialCat] begin

    limit(::EmptyDiagram)::AbsLimit = InitialColimit{Nothing,Nothing}(nothing)

    universal(::AbsLimit, ::EmptyDiagram, ::Multispan) = nothing
end

@instance ThCategoryUnbiasedProducts{Nothing,Nothing} [model::TrivialCat] begin 

  limit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    LimitCone(Multispan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsLimit, ::DiscreteDiagram, ::Multispan) = nothing
end


@instance ThCategoryWithEqualizers{Nothing,Nothing} [model::TrivialCat] begin 

  limit(d::ParallelMorphisms) = 
    LimitCone(Multispan([nothing], [nothing], [nothing]), FreeDiagram(d))

  universal(::AbsLimit, ::ParallelMorphisms, ::Multispan) = nothing
end

@instance ThCategoryWithPullbacks{Nothing,Nothing} [model::TrivialCat] begin 

  limit(d::Multicospan) = let n = length(d); ns=fill(nothing, n);
    LimitCone(Multispan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsLimit, ::Multicospan, ::Multispan) = nothing
end


@instance ThCategoryWithBipartiteColimits{Nothing, Nothing} [model::TrivialCat]  begin 

  colimit(d::BipartiteFreeDiagram)::AbsColimit = let ns=fill(nothing, nv₂(d));
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::BipartiteFreeDiagram, ::Multicospan) = nothing
end



end # module

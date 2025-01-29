module DiscreteCatLimits 

using GATlab

using ....BasicSets
using ...Cats

import .ThCategoryUnbiasedCoproducts

@instance ThCategoryWithInitial{Ob,Ob} [model::DiscreteCat{Ob}] where {Ob} begin 
  function colimit(::EmptyDiagram)::AbsColimit
    if model.set isa FinSet && length(model.set) == 1
      InitialColimit(only(model.set))
    else 
      error("There exists no initial object ")
    end 
  end

  function universal(lim::AbsColimit, ::EmptyDiagram, ::Multicospan)::Ob
    ob(lim)
  end 
end

@instance ThCategoryUnbiasedCoproducts{Ob,Ob} [model::DiscreteCat{Ob}] where {Ob} begin 


  function colimit(d::DiscreteDiagram)::AbsColimit
    if isempty(d)
      colimit[model](EmptyDiagram{Ob}())
    elseif allequal(d)
      os = collect(d)
      ColimitCocone(Multicospan{Ob,Ob}(first(os), os, os), FreeDiagram(d))
    else 
      error("Nonidentity morphism in $d")
    end
  end

  function universal(lim::AbsColimit, ::DiscreteDiagram, ::Multicospan)::Ob
    apex(lim)
  end 
end

end # module

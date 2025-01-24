module FreeGraphs 
export ToBipartiteLimit, ToBipartiteColimit, BipartiteLimit, BipartiteColimit

using ACSets
using ...Functors, ...FreeDiagrams

using .....Theories: compose, ⋅
using .....Graphs
using ..Limits, ..Colimits
import ..Limits: limit 
import ..Colimits: colimit 
import ..LimitsColimits: universal


""" Compute a limit by reducing the diagram to a free bipartite diagram.
"""
struct ToBipartiteLimit <: LimitAlgorithm end

""" Limit computed by reduction to the limit of a free bipartite diagram.
"""
struct BipartiteLimit{Ob, Diagram, Cone<:Multispan{Ob},
                      Lim<:AbstractLimit} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limit::Lim
end


# FIXME: make this similar to how colimits are treated
function limit(F::Union{Functor,FreeDiagram,FixedShapeFreeDiagram}, ::ToBipartiteLimit)
  d = BipartiteFreeDiagram(F)
  lim = limit(d)
  cone = Multispan(apex(lim), map(incident(d, :, :orig_vert₁),
                                  incident(d, :, :orig_vert₂)) do v₁, v₂
    if isempty(v₁)
      e = first(incident(d, only(v₂), :tgt))
      compose(legs(lim)[src(d, e)], hom(d, e))
    else
      legs(lim)[only(v₁)]
    end
  end)
  BipartiteLimit(F, cone, lim)
end

function universal(lim::BipartiteLimit, cone::Multispan)
  lim = lim.limit
  cone = Multispan(apex(cone), legs(cone)[lim.diagram[:orig_vert₁]])
  universal(lim, cone)
end

""" Compute a colimit by reducing the diagram to a free bipartite diagram.
"""
struct ToBipartiteColimit <: ColimitAlgorithm end

""" Limit computed by reduction to the limit of a free bipartite diagram.
"""
struct BipartiteColimit{Ob, Diagram, Cocone<:Multicospan{Ob},
                        Colim<:AbstractColimit} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimit::Colim
end

function colimit(F::FixedShapeFreeDiagram, ::ToBipartiteColimit)
  kwarg = F isa DiscreteDiagram ? Dict(:colimit=>true) : Dict()
  d = BipartiteFreeDiagram(F; kwarg...)
  colim = colimit(d)
  return BipartiteColimit(F, cocone(colim), colim)
end 

function colimit(F::Union{T,FreeDiagram}, ::ToBipartiteColimit) where {T<:Functor}
  d = BipartiteFreeDiagram(F, colimit=true)
  colim = colimit(d)
  cocone = Multicospan(apex(colim), map(incident(d, :, :orig_vert₁),
                                        incident(d, :, :orig_vert₂)) do v₁, v₂
    if isempty(v₂)
      e = first(incident(d, only(v₁), :src))
      compose(hom(d, e), legs(colim)[tgt(d, e)])
    else
      legs(colim)[only(v₂)]
    end
  end)
  BipartiteColimit(F, cocone, colim)
end

function universal(colim::BipartiteColimit, cocone::Multicospan)
  colim = colim.colimit
  cocone = Multicospan(apex(cocone), legs(cocone)[cocone_indices(colim.diagram)])
  universal(colim, cocone)
end

end # module

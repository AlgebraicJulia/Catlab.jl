module FreeGraphs
export ThCategoryWithBipartiteLimits, ThCategoryWithBipartiteColimits, ThCategoryWithLimits, ThCategoryWithColimits

using GATlab
import .....Theories: universal
using ..FreeDiagrams
using ..LimitsColimits: ThCategoryLimitBase, ThCategoryColimitBase
import ..LimitsColimits: colimit, limit


"""
Limits on a free bipartite graph presentation of a diagram.

"""
@theory ThCategoryWithBipartiteLimits <: ThCategoryLimitBase begin
  BiPart::TYPE{BipartiteFreeDiagram}

  limit(d::BiPart)::Limit
  universal(lim::Limit, d::BiPart, sp::MSpan)::(apex(sp) → ob(lim))
end

"""
Limits on a free graph presentation of a diagram.
"""
@theory ThCategoryWithLimits <: ThCategoryLimitBase begin
  FGraph::TYPE{FreeGraph}

  limit(d::FGraph)::Limit
  universal(lim::Limit, d::FGraph, sp::MSpan)::(apex(sp) → ob(lim))
end


"""
Colimits on a free bipartite graph presentation of a diagram.

"""
@theory ThCategoryWithBipartiteColimits <: ThCategoryColimitBase begin
  BiPart::TYPE{BipartiteFreeDiagram}

  colimit(d::BiPart)::Colimit
  universal(lim::Colimit, d::BiPart, sp::MCospan)::(ob(lim) → apex(sp))
end

"""
Colimits on a free graph presentation of a diagram.
"""
@theory ThCategoryWithColimits <: ThCategoryColimitBase begin
  FGraph::TYPE{FreeGraph}

  colimit(d::FGraph)::Colimit
  universal(lim::Colimit, d::FGraph, sp::MCospan)::(ob(lim) → apex(sp))
end

end # module

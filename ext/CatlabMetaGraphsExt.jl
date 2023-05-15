module CatlabMetaGraphsExt

using Catlab.Graphs

import MetaGraphs
import MetaGraphs: MetaGraph, MetaDiGraph

MetaGraph(g::AbstractSymmetricWeightedGraph{S, Tuple{U}}) where {S,U} =
  to_weighted_metagraph(MetaGraph{Int,U}, g)
MetaDiGraph(g::AbstractWeightedGraph{S, Tuple{U}}) where {S,U} =
  to_weighted_metagraph(MetaDiGraph{Int,U}, g)

function to_weighted_metagraph(MG::Type{<:MetaGraphs.AbstractMetaGraph}, g)
  mg = MG(nv(g))
  for (s, t, w) in zip(src(g), tgt(g), weight(g))
    MetaGraphs.add_edge!(mg, s, t, :weight, w)
  end
  mg
end

end

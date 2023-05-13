module CatlabGraphsExt

using Catlab.Graphs

import Graphs as SimpleGraphs
import Graphs: SimpleGraph, SimpleDiGraph

function (::Type{SG})(g::HasGraph) where SG <: Union{SimpleGraph,SimpleDiGraph}
  sg = SG(nv(g))
  for (s, t) in zip(src(g), tgt(g))
    SimpleGraphs.add_edge!(sg, s, t)
  end
  sg
end

function (::Type{G})(sg::Union{SimpleGraph,SimpleDiGraph}) where G <: HasGraph
  g = G(SimpleGraphs.nv(sg))
  for e in SimpleGraphs.edges(sg)
    add_edge!(g, SimpleGraphs.src(e), SimpleGraphs.dst(e))
  end
  g
end

function SimpleGraph(g::AbstractHalfEdgeGraph)
  sg = SimpleGraph(nv(g))
  for e in half_edges(g)
    e′ = inv(g,e)
    if e <= e′
      SimpleGraphs.add_edge!(sg, vertex(g,e), vertex(g,e′))
    end
  end
  sg
end

end

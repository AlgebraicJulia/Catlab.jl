import .Graphviz

# External library import.
import .GraphViz
import .GraphViz: Graph

""" Convert our Graphviz graph type to `GraphViz`'s graph type.
"""
function Graph(graph::Graphviz.Graph; engine::String="dot")::Graph
  gv = Graph(sprint(Graphviz.pprint, graph))
  if !isempty(engine)
    GraphViz.layout!(gv, engine=engine)
  end
  return gv
end

function Base.show(io::IO, ::MIME"image/svg+xml", graph::Graphviz.Graph)
  show(io, MIME"image/svg+xml"(), Graph(graph))
end

# Graphviz PNG output requires Cairo.
#function Base.show(io::IO, ::MIME"image/png", graph::Graphviz.Graph)
#  show(io, MIME"image/png"(), Graph(graph))
#end

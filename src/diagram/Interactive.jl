module Interactive
export Graph, TikzPicture

import Pkg

using ...Catlab

# Graphviz diagrams
###################

import ..Graphviz
@optional_import import GraphViz
@optional_import import GraphViz: Graph

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
if haskey(Pkg.installed(), "Cairo")
  function Base.show(io::IO, ::MIME"image/png", graph::Graphviz.Graph)
    show(io, MIME"image/png"(), Graph(graph))
  end
end

# TikZ diagrams
###############

import ..TikZ
@optional_import import TikzPictures: TikzPicture

""" Convert our TikZ picture type to `TikzPicture`'s picture type. 
"""
function TikzPicture(pic::TikZ.Picture; preamble::String="", usePDF2SVG=true)::TikzPicture
  data = join(sprint(TikZ.pprint, stmt) for stmt in pic.stmts)
  options = join((sprint(TikZ.pprint, prop) for prop in pic.props), ",")
  preamble = join([
    preamble,
    "\\usepackage{amssymb}",
    # FIXME: These TikZ library dependencies should be stored in TikZ.Picture.
    "\\usetikzlibrary{arrows.meta}",
    "\\usetikzlibrary{calc}",
    "\\usetikzlibrary{decorations.markings}",
    "\\usetikzlibrary{positioning}",
    "\\usetikzlibrary{shapes.geometric}",
  ], "\n")
  TikzPicture(data; options=options, preamble=preamble, usePDF2SVG=usePDF2SVG)
end

function Base.show(io::IO, ::MIME"image/svg+xml", pic::TikZ.Picture)
  show(io, MIME"image/svg+xml"(), TikzPicture(pic))
end

end

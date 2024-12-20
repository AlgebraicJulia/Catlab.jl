module Paths 

export Path

using StructEquality
using StaticArrays: SVector

using ....Graphs
import ....Graphs: src, tgt, edges

# Paths in graphs
#----------------

""" Path in a graph.

The path is allowed to be empty but always has definite start and end points
(source and target vertices).
"""
@struct_hash_equal struct Path{V,E,Edges<:AbstractVector{E}}
  edges::Edges
  src::V
  tgt::V
end

Path{V,E}(v::V) where {V,E} = Path(E[], v, v)

# Accessors
#----------
edges(path::Path) = path.edges

src(path::Path) = path.src

tgt(path::Path) = path.tgt

# Other methods
#--------------

function Base.show(io::IO, path::Path)
  print(io, "Path(")
  show(io, edges(path))
  print(io, ": $(src(path)) → $(tgt(path)))")
end

Base.length(p::Path) = length(edges(p))

Base.reverse(p::Path) = Path(reverse(edges(p)), tgt(p), src(p))

Base.iterate(p::Path, x...) = iterate(edges(p), x...)

# Graph-specific Path constructions
###################################

function Path(g::HasGraph, es::AbstractVector)
  !isempty(es) || error("Nonempty edge list needed for nontrivial path")
  all(e -> has_edge(g, e), es) || error("Path has edges not contained in graph")
  Path(es, src(g, first(es)), tgt(g, last(es)))
end

function Path(g::HasGraph, e)
  has_edge(g, e) || error("Edge $e not contained in graph $g")
  Path(SVector(e), src(g,e), tgt(g,e))
end

function Base.empty(::Type{Path}, g::HasGraph, v::T) where T
  has_vertex(g, v) || error("Vertex $v not contained in graph $g")
  Path(SVector{0,T}(), v, v)
end

function Base.vcat(p1::Path, p2::Path)
  tgt(p1) == src(p2) ||
    error("Path start/end points do not match: $(tgt(p1)) != $(src(p2))")
  Path(vcat(edges(p1), edges(p2)), src(p1), tgt(p2))
end

coerce_path(::HasGraph, path::Path) = path

coerce_path(g::HasGraph, x) = Path(g, x)

end  # module

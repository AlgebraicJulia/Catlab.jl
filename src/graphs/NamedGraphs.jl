""" Extends the basic graph types with vertex and/or edge names.

Naming vertices and edges and looking them up by name is a common requirement.
This module provides a simple interface and default graph types for named
graphs. Names are understood to be unique within the graph but are *not* assumed
to be strings or symbols.
"""
module NamedGraphs
export vertex_name, edge_name, vertex_named, edge_named,
  AbstractNamedGraph, NamedGraph

using ACSets
using ...GATs, ..BasicGraphs

# Names interface
#################

""" Name of a vertex in a graph.

By default, the name of a vertex is its ID.
"""
vertex_name(g::HasVertices, v) = v

""" Name of an edge in a graph.

By default, the name of an edge is its ID.
"""
edge_name(g::HasGraph, e) = e

""" Get vertex in graph with given name.
"""
function vertex_named(g::HasVertices, name)
  @assert has_vertex(g, name)
  name
end

""" Get edge in graph with given name.
"""
function edge_named(g::HasGraph, name)
  @assert has_edge(g, name)
  name
end

# Named graphs
##############

@present SchNamedGraph <: SchGraph begin
  VName::AttrType
  EName::AttrType
  vname::Attr(V, VName)
  ename::Attr(E, EName)
end

""" Abstract type for graph with named vertices and edges.
"""
@abstract_acset_type AbstractNamedGraph <: AbstractGraph

""" Graph with named vertices and edges.
"""
@acset_type NamedGraph(SchNamedGraph, index=[:src,:tgt,:ename],
                       unique_index=[:vname]) <: AbstractNamedGraph

vertex_name(g::AbstractNamedGraph, args...) = subpart(g, args..., :vname)
edge_name(g::AbstractNamedGraph, args...) = subpart(g, args..., :ename)

vertex_named(g::AbstractNamedGraph, name) = only(incident(g, name, :vname))
edge_named(g::AbstractNamedGraph, name)= only(incident(g, name, :ename))

end

""" AST and pretty printer for Graphviz's DOT language.

References:

- DOT grammar: http://www.graphviz.org/doc/info/lang.html
- DOT language guide: http://www.graphviz.org/pdf/dotguide.pdf
"""
module Graphviz
export Expression, Statement, Attributes, Graph, Digraph, Subgraph,
  Node, NodeID, Edge, Label, pprint, run_graphviz

using DataStructures: OrderedDict
using AutoHashEquals
using Requires: @require

const USE_GV_JLL = Ref(false)

function __init__()
  @require Graphviz_jll="3c863552-8265-54e4-a6dc-903eb78fde85" begin
    USE_GV_JLL[] = true
    let cfg = joinpath(Graphviz_jll.artifact_dir, "lib", "graphviz", "config6")
      if !isfile(cfg)
        Graphviz_jll.dot(path -> run(`$path -c`))
      end
    end
  end
end

# AST
#####

abstract type Expression end
abstract type Statement <: Expression end

""" AST type for Graphviz's "HTML-like" node labels.

For now, the HTML content is just a string.
"""
struct Html
  content::String
end
Base.print(io::IO, html::Html) = print(io, html.content)

const AttributeValue = Union{String,Html}
const Attributes = OrderedDict{Symbol,AttributeValue}

as_attributes(attrs::Attributes) = attrs
as_attributes(d::OrderedDict) = Attributes(Symbol(k) => d[k] for k in keys(d))
as_attributes(d::AbstractDict) =
  Attributes(Symbol(k) => d[k] for k in sort!(collect(keys(d))))

Base.@kwdef struct Graph <: Expression
  name::String
  directed::Bool
  prog::String="dot"
  stmts::Vector{Statement}=Statement[]
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Graph(name::String, stmts::Vector{Statement}; kw...) =
  Graph(; name=name, directed=false, stmts=stmts, kw...)
Graph(name::String, stmts::Vararg{Statement}; kw...) =
  Graph(; name=name, directed=false, stmts=collect(stmts), kw...)
Digraph(name::String, stmts::Vector{Statement}; kw...) =
  Graph(; name=name, directed=true, stmts=stmts, kw...)
Digraph(name::String, stmts::Vararg{Statement}; kw...) =
  Graph(; name=name, directed=true, stmts=collect(stmts), kw...)

Base.@kwdef struct Subgraph <: Statement
  name::String="" # Subgraphs can be anonymous
  stmts::Vector{Statement}=Statement[]
  graph_attrs::Attributes=Attributes()
  node_attrs::Attributes=Attributes()
  edge_attrs::Attributes=Attributes()
end

Subgraph(stmts::Vector{Statement}; kw...) = Subgraph(; stmts=stmts, kw...)
Subgraph(stmts::Vararg{Statement}; kw...) = Subgraph(; stmts=collect(stmts), kw...)
Subgraph(name::String, stmts::Vector{Statement}; kw...) =
  Subgraph(; name=name, stmts=stmts, kw...)
Subgraph(name::String, stmts::Vararg{Statement}; kw...) =
  Subgraph(; name=name, stmts=collect(stmts), kw...)

struct Node <: Statement
  name::String
  attrs::Attributes
end
Node(name::String, attrs::AbstractDict) = Node(name, as_attributes(attrs))
Node(name::String; attrs...) = Node(name, attrs)

@auto_hash_equals struct NodeID <: Expression
  name::String
  port::String
  anchor::String
  NodeID(name::String, port::String="", anchor::String="") = new(name, port, anchor)
end

@auto_hash_equals struct Edge <: Statement
  path::Vector{NodeID}
  attrs::Attributes
end
Edge(path::Vector{NodeID}, attrs::AbstractDict) = Edge(path, as_attributes(attrs))
Edge(path::Vector{NodeID}; attrs...) = Edge(path, attrs)
Edge(path::Vararg{NodeID}; attrs...) = Edge(collect(path), attrs)
Edge(path::Vector{String}, attrs::AbstractDict) = Edge(map(NodeID, path), attrs)
Edge(path::Vector{String}; attrs...) = Edge(map(NodeID, path), attrs)
Edge(path::Vararg{String}; attrs...) = Edge(map(NodeID, collect(path)), attrs)

"""
labelloc defaults: "t" (clusters) , "b" (root graphs) , "c" (nodes)
For graphs and clusters, only labelloc=t and labelloc=b are allowed
"""
Base.@kwdef struct Label <: Statement
  labelloc::String = ""
  label::String = ""
end

# Useful in unit tests. Not exported.

function filter_statements(graph::Graph, type::Type)
  [ stmt for stmt in graph.stmts if stmt isa type ]
end
function filter_statements(graph::Graph, type::Type, attr::Symbol)
  [ stmt.attrs[attr] for stmt in graph.stmts
    if stmt isa type && haskey(stmt.attrs, attr) ]
end

# Bindings
##########

""" Run a Graphviz program.

Invokes Graphviz through its command-line interface. If the `Graphviz_jll`
package is installed and loaded, it is used; otherwise, Graphviz must be
installed on the local system.

For bindings to the Graphviz C API, see the the package
[GraphViz.jl](https://github.com/Keno/GraphViz.jl). At the time of this writing,
GraphViz.jl is unmaintained.
"""
function run_graphviz(io::IO, graph::Graph; prog::Union{String,Nothing}=nothing,
                      format::String="json0")
  if isnothing(prog)
    prog = graph.prog
  end
  @assert prog in ("dot","neato","fdp","sfdp","twopi","circo")
  if USE_GV_JLL[]
    fun = getfield(Graphviz_jll, Symbol(prog))
    prog = fun(identity)
  end
  open(`$prog -T$format`, io, write=true) do gv
    pprint(gv, graph)
  end
end
function run_graphviz(graph::Graph; kw...)
  io = IOBuffer()
  run_graphviz(io, graph; kw...)
  seekstart(io)
end

function Base.show(io::IO, ::MIME"image/svg+xml", graph::Graph)
  run_graphviz(io, graph, format="svg")
end

# Pretty-print
##############

""" Pretty-print the Graphviz expression.
"""
pprint(expr::Expression) = pprint(stdout, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

function pprint(io::IO, graph::Graph, n::Int)
  indent(io, n)
  print(io, graph.directed ? "digraph " : "graph ")
  print(io, graph.name)
  println(io, " {")
  pprint_attrs(io, graph.graph_attrs, n+2; pre="graph", post=";\n")
  pprint_attrs(io, graph.node_attrs, n+2; pre="node", post=";\n")
  pprint_attrs(io, graph.edge_attrs, n+2; pre="edge", post=";\n")
  for stmt in graph.stmts
    pprint(io, stmt, n+2, directed=graph.directed)
    println(io)
  end
  indent(io, n)
  println(io, "}")
end

function pprint(io::IO, subgraph::Subgraph, n::Int; directed::Bool=false)
  indent(io, n)
  if isempty(subgraph.name)
    println(io, "{")
  else
    print(io, "subgraph ")
    print(io, subgraph.name)
    println(io, " {")
  end
  pprint_attrs(io, subgraph.graph_attrs, n+2; pre="graph", post=";\n")
  pprint_attrs(io, subgraph.node_attrs, n+2; pre="node", post=";\n")
  pprint_attrs(io, subgraph.edge_attrs, n+2; pre="edge", post=";\n")
  for stmt in subgraph.stmts
    pprint(io, stmt, n+2, directed=directed)
    println(io)
  end
  indent(io, n)
  print(io, "}")
end

function pprint(io::IO, node::Node, n::Int; directed::Bool=false)
  indent(io, n)
  print(io, node.name)
  pprint_attrs(io, node.attrs)
  print(io, ";")
end

function pprint(io::IO, node::NodeID, n::Int)
  print(io, node.name)
  if !isempty(node.port)
    print(io, ":")
    print(io, node.port)
  end
  if !isempty(node.anchor)
    print(io, ":")
    print(io, node.anchor)
  end
end

function pprint(io::IO, edge::Edge, n::Int; directed::Bool=false)
  indent(io, n)
  for (i, node) in enumerate(edge.path)
    if i > 1
      print(io, directed ? " -> " : " -- ")
    end
    pprint(io, node, n)
  end
  pprint_attrs(io, edge.attrs)
  print(io, ";")
end

function pprint_attrs(io::IO, attrs::Attributes, n::Int=0;
                      pre::String="", post::String="")
  if !isempty(attrs)
    indent(io, n)
    print(io, pre)
    print(io, " [")
    for (i, (key, value)) in enumerate(attrs)
      if (i > 1) print(io, ",") end
      print(io, key)
      print(io, "=")
      print(io, value isa Html ? "<" : "\"")
      print(io, value)
      print(io, value isa Html ? ">" : "\"")
    end
    print(io, "]")
    print(io, post)
  end
end

function pprint(io::IO, lab::Label, n::Int; directed::Bool=false)
  if !isempty(lab.labelloc)
    print(io, "labelloc=\"$(lab.labelloc)\";")
  end
  print(io, "label=\"$(lab.label)\";")
end

indent(io::IO, n::Int) = print(io, " "^n)

end

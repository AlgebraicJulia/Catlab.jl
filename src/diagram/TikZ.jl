module TikZ
export Expression, Statement, GraphStatement, Coordinate, Property, 
       PathOperation, Picture, Node, Edge, EdgeNode, Graph, GraphNode,
       GraphEdge, to_tikz

using AutoHashEquals
using Match
import ...Syntax: pprint
import ..Wiring

# AST
#####

""" Base class for TikZ abstract syntax tree.

The AST is very incomplete! It is adapted from the (also incomplete) BNF
grammar for TikZ in [TikZit](http://tikzit.sourceforge.net/manual.html).
"""
abstract Expression
abstract Statement <: Expression
abstract GraphStatement <: Expression

@auto_hash_equals immutable Coordinate <: Expression
  x::AbstractString
  y::AbstractString
end

@auto_hash_equals immutable Property <: Expression
  key::AbstractString
  value::Nullable{AbstractString}
  
  Property(key::AbstractString) = new(key, Nullable())
  Property(key::AbstractString, value::AbstractString) = new(key, Nullable(value))
end

@auto_hash_equals immutable PathOperation <: Expression
  op::AbstractString
  props::Vector{Property}
  
  PathOperation(op::AbstractString; props=Property[]) = new(op, props)
end

@auto_hash_equals immutable Picture <: Expression
  stmts::Vector{Statement}
  props::Vector{Property}
  
  Picture(stmts::Vararg{Statement}; props=Property[]) = new([stmts...], props)
end

@auto_hash_equals immutable Node <: Statement
  name::AbstractString
  props::Vector{Property}
  coord::Nullable{Coordinate}
  content::Nullable{AbstractString}
  
  Node(name::AbstractString; props=Property[], coord=Nullable(),
       content=Nullable()) = new(name, props, coord, content)
end

@auto_hash_equals immutable EdgeNode <: Expression
  props::Vector{Property}
  content::Nullable{AbstractString}
  
  EdgeNode(; props=Property[], content=Nullable()) = new(props, content)
end

@auto_hash_equals immutable Edge <: Statement
  src::AbstractString
  tgt::AbstractString
  op::PathOperation
  props::Vector{Property}
  node::Nullable{EdgeNode}
  
  Edge(src::AbstractString, tgt::AbstractString;
       op=PathOperation("to"), props=Property[], node=Nullable()) =
    new(src, tgt, op, props, node)
end

@auto_hash_equals immutable Graph <: Statement
  stmts::Vector{GraphStatement}
  props::Vector{Property}
  
  Graph(stmts::Vararg{GraphStatement}; props=Property[]) =
    new([stmts...], props)
end

@auto_hash_equals immutable GraphNode <: GraphStatement
  name::AbstractString
  props::Vector{Property}
  content::Nullable{AbstractString}
  
  GraphNode(name::AbstractString; props=Property[], content=Nullable()) =
    new(name, props, content)
end

@auto_hash_equals immutable GraphEdge <: GraphStatement
  src::AbstractString
  tgt::AbstractString
  props::Vector{Property}
  
  GraphEdge(src::AbstractString, tgt::AbstractString; props=Property[]) =
    new(src, tgt, props)
end

# Wiring Diagrams
#################

""" TODO
"""
function to_tikz(diagram::Wiring.WiringDiagram)::Picture
  graph = to_tikz_graph(diagram)
  
  # Edges (visible).
  stmts = Statement[]
  props = [ Property("postaction", "{decorate}") ]
  op = PathOperation("to"; props=[Property("out","0"),Property("in","180")])
  for conn in sort_connections(diagram.connections)
    src = connector_anchor(diagram, conn.src)
    tgt = connector_anchor(diagram, conn.tgt)
    if conn.src.box == 0
      content = dom(diagram)[conn.src.port]
    else
      content = codom(diagram.boxes[conn.src.box])[conn.src.port]
    end
    push!(stmts, Edge(src, tgt; props=props, op=op, content=string(content)))
  end
  
  props = [ Property("decoration",
                     "{markings,mark=at position 0.5 with {\arrow{>}}}") ]
  Picture(graph, stmts...; props=props)
end

""" TODO
"""
function to_tikz_graph(diagram::Wiring.WiringDiagram)::Graph
  stmts = GraphStatments[]
  
  # Outer box nodes (invisible).
  for i in eachindex(dom(diagram)) # In-ports of outer box
    push!(stmts, GraphNode("in$i"; props=[Property("draw","none")], content=""))
  end
  for i in eachindex(codom(diagram)) # Out-ports of outer box
    push!(stmts, GraphNode("out$i"; props=[Property("draw","none")], content=""))
  end
  
  # Atomic nodes (visible).
  box_height(box) = 2*max(length(box.dom),length(box.codom))
  for (i,box) in enumerate(diagram.boxes)
    props = [ Property("minimum height", "$(box_height(box))em") ]
    push!(stmts, GraphNode("b$i"; props=props, content=string(box.content)))
  end
  
  # Edges (invisible: for layout only).
  for conn in sort_connections(diagram.connections)
    push!(stmts, EdgeNode(connector_node(conn.src), connector_node(conn.tgt)))
  end

  props = [
    Property("layered layout"),
    Property("grow'", "right"),
    Property("layer distance", "4em"),
    Property("sibling sep", "1em"),
    Property("nodes", "{draw,rectangle}"),
    Property("edges", "{draw=none}"),
  ]
  graph = Graph(stmts...; props=props)
end

""" Sort the connections in a wiring diagram.

The connections in a wiring diagram have no canonical order, but the order of
the edges affects the graph layout algorithm (as in Graphviz). This function
orders the connections to obtain a layout that is (1) deterministic and (2)
gives the natural ordering at the boundaries.
"""
function sort_connections(conns::Set{Wiring.Connection})::Vector{Wiring.Connection}
  lt(c1::Wiring.Connector, c2::Wiring.Connector) = 
    c1.box < c2.box || c1.kind < c2.kind || c1.port < c2.port
  lt(c1::Wiring.Connection, c2::Wiring.Connection) =
    lt(c1.src, c2.src) || lt(c1.tgt, c2.tgt)
  sort(conns, lt=lt)
end

""" TikZ node associated with Connector.
"""
function connector_node(conn::Wiring.Connector)
  @match conn begin
    Wiring.Connector(0, Wiring.Input, port) => "in$port"
    Wiring.Connector(0, Wiring.Output, port) => "out$port"
    Wiring.Connector(box, _, _) => "b$box"
  end
end

""" TikZ node, including anchor, associated with Connector.
"""
function connector_anchor(diagram::Wiring.WiringDiagram, conn::Wiring.Connector)
  node = connector_node(conn)
  if conn.box == 0
    return node
  end
  box = diagram.boxes[conn.box]
  m, n = length(box.dom), length(box.codom)
  if conn.kind == Input
    frac = @sprintf "%.3f" (conn.port / (m+1))
    m == 1 ? node : "\$($node.north west)!$(frac)!($node.south west)\$"
  else
    frac = @sprintf "%.3f" (conn.port / (n+1))
    n == 1 ? node : "\$($node.north east)!$(frac)!($node.south east)\$"
  end
end

# Pretty-print
##############

""" Pretty-print the TikZ expression.
"""
pprint(expr::Expression) = pprint(STDOUT, expr)
pprint(io::IO, expr::Expression) = pprint(io, expr, 0)

function pprint(io::IO, pic::Picture, n::Int)
  indent(io, n)
  print(io, "\\begin{tikzpicture}")
  pprint(io, pic.props)
  println(io)
  for stmt in pic.stmts
    pprint(io, stmt, n+2)
  end
  indent(io, n)
  println(io, "\\end{tikzpicture}")
end

function pprint(io::IO, node::Node, n::Int)
  indent(io, n)
  print(io, "\\node")
  pprint(io, node.props)
  print(io, " ($(node.name))")
  if !isnull(node.coord)
    print(io, " at ")
    pprint(io, get(node.coord))
  end
  if !isnull(node.content)
    print(io, " {$(get(node.content))}")
  end
  println(io, ";")
end

function pprint(io::IO, edge::Edge, n::Int)
  indent(io, n)
  print(io, "\\draw")
  pprint(io, edge.props)
  print(io, " ($(edge.src)) ")
  pprint(io, edge.op)
  if !isnull(edge.node)
    print(io, " ")
    pprint(io, get(edge.node))
  end
  println(io, " ($(edge.tgt));")
end

function pprint(io::IO, node::EdgeNode, n::Int)
  print(io, "node")
  pprint(io, node.props)
  if !isnull(node.content)
    print(io, " {$(get(node.content))}")
  end
end

function pprint(io::IO, graph::Graph, n::Int)
  indent(io, n)
  print(io, "\\graph")
  pprint(io, graph.props)
  println(io, '{')
  for stmt in graph.stmts
    pprint(io, stmt, n+2)
  end
  indent(io, n)
  println(io, "};")
end

function pprint(io::IO, node::GraphNode, n::Int)
  indent(io, n)
  print(io, node.name)
  if !isnull(node.content)
    print(io, "/\"$(get(node.content))\"")
  end
  if !isempty(node.props)
    print(io, " ")
    pprint(io, node.props)
  end
  println(io, ";")
end

function pprint(io::IO, node::GraphEdge, n::Int)
  indent(io ,n)
  print(io, "$(node.src) ->")
  pprint(io, node.props)
  println(io, " $(node.tgt);")
end

function pprint(io::IO, coord::Coordinate, n::Int)
  print(io, "($(coord.x),$(coord.y))")
end

function pprint(io::IO, op::PathOperation, n::Int)
  print(io, op.op)
  pprint(io, op.props)
end

function pprint(io::IO, prop::Property, n::Int)
  print(io, prop.key)
  if !isnull(prop.value)
    print(io, "=")
    print(io, get(prop.value))
  end
end

function pprint(io::IO, props::Vector{Property}, n::Int=0)
  if !isempty(props)
    print(io, "[")
    for (i, prop) in enumerate(props)
      pprint(io, prop)
      if (i < length(props)) print(io, ",") end
    end
    print(io, "]")
  end
end

indent(io::IO, n::Int) = print(io, " "^n)

end

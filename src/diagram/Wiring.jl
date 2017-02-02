""" Draw wiring diagrams (aka string diagrams) in various formats.
"""
module Wiring
export diagram_tikz

using Match
import ...Syntax: ObExpr, MorExpr, dom, codom, head, args, compose, id
import ..TikZ

# TikZ
######

immutable MorTikZ
  node::TikZ.Node
  dom::Vector{AbstractString}
  codom::Vector{AbstractString}
end

"""
"""
function diagram_tikz(f::MorExpr; math_mode::Bool=false)::TikZ.Picture
  f_in = otimes([ id(A) for A in dom(f) ]...)
  f_out = otimes([ id(B) for B in codom(f) ]...)
  mor = mor_tikz(compose(f_in, f, f_out))
  stmts = Statement[ mor.node ]

  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("decoration", "{markings, mark=at position 0.5 with {\arrow{>}}}"),
    TiKZ.Property("every to/.style", "{out=0,in=180}")
  ]
  if math_mode
    append!(props, [ TikZ.Property("execute at begin node", "$"),
                     TikZ.Property("execute at end node", "$") ])
  end
  TikZ.Picture(stmts; props=props)
end

function mor_tikz(f::MorExpr; kwargs...)::MorTikZ
  mor_tikz(f, Val{head(f)}; kwargs...)
end

function mor_tikz(f::MorExpr, ::Type{Val{:gen}}; prefix::String="", kwargs...)

  props = [
    TikZ.Property("draw"),
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(prefix; content=string(args(f)[1]), props=props)
  MorTikZ(node, dom, codom)
end

function mor_tikz(f::MorExpr, ::Type{Val{:compose}}; prefix::String="")
  nn(i) = node_name(prefix, i)

  mors = [ mor_tikz(g; prefix=nn(i)) for g in args(f) ]
  stmts = TikZ.Statment[ mors[1].node ]
  for i = 2:length(mors)
    push!(mors[i].node.props, TikZ.Property("right=2em of $(nn(i-1))"))
    push!(smts, mors[i].node)
    for j = 1:length(mors[i].codom)
      edge = TikZ.Edge(mors[i-1].dom[j], mors[i].codom[j];
                       props=[TikZ.Property("postaction","{decorate}")],
                       op=TikZ.PathOperation("to"))
      push!(smts, edge)
    end
  end

  node = Node(prefix; content=TikZ.Picture(stmts))
  MorTikZ(node, first(mors).dom, last(mors).codom)
end

function mor_tikz(f::MorExpr, ::Type{Val{:otimes}}; prefix::String="")
  nn(i) = node_name(prefix, i)

  mors = []
  for (i,g) in enumerate(args(f))
    mor = mor_tikz(g; prefix=nn(i))
    if i > 1
      push!(mor.node.props, TikZ.Property("below=1em of $(nn(i-1))"))
      end
    push!(mors, mor)
  end
  stmts = TikZ.Statment[ mor.node for mor in mors ]

  node = Node(prefix; content=TikZ.Picture(stmts))
  dom = vcat([ mor.dom for mor in mors]...)
  codom = vcat([ mor.codom for codom in mors]...)
  MorTikZ(node, dom, codom)
end

node_name(prefix::String, n::Int) = "$(prefix)$n"

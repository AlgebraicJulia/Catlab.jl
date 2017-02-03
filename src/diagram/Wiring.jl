""" Draw wiring diagrams (aka string diagrams) in various formats.
"""
module Wiring
export diagram_tikz

import Formatting: format
using Match
import ...Syntax: ObExpr, MorExpr, dom, codom, head, args, compose, id, otimes
import ..TikZ

# TikZ
######

immutable PortTikZ
  anchor::AbstractString
  content::AbstractString
end

immutable MorTikZ
  node::TikZ.Node
  dom::Vector{PortTikZ}
  codom::Vector{PortTikZ}
end

""" Draw a wiring diagram in TikZ for the given formula.

THe diagram is constructed recursively, mirroring the structure of the formula.
This is achieved by nesting TikZ pictures in TikZ nodes recursively--a feature
not officially supported by TikZ but which is commonly used nonetheless.

Warning: Since our implementation uses the `remember picture` option, LaTeX must
be *twice* to fully render the picture. See (TikZ Manual, Sec 17.13).
"""
function diagram_tikz(f::MorExpr; font_size::Number=12, math_mode::Bool=true,
                      box_size::Number=2, compose_sep::Number=2,
                      product_sep::Number=0.5)::TikZ.Picture
  # Draw input and output arrows by adding identities on either side of f. 
  f_ext = compose(id(dom(f)), f, id(codom(f)))
  
  style = Dict(:box_size => box_size,
               :compose_sep => compose_sep, :product_sep => product_sep)
  mor = mor_tikz(f_ext, "n", style)
  
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("decoration", 
                  "{markings, mark=at position 0.5 with {\\arrow{stealth}}}"),
    TikZ.Property("font", 
                  "{\\fontsize{$(format(font_size))}{$(format(1.2*font_size))}}"),
    TikZ.Property("generator/.style",
                  "{draw,solid,rounded corners,inner sep=0.333em}"),
    TikZ.Property("container/.style", "{inner sep=0}"),
    TikZ.Property("every path/.style", "{solid}"),
    TikZ.Property("every to/.style", "{out=0,in=180}"),
  ]
  if math_mode
    append!(props, [ TikZ.Property("execute at begin node", "\$"),
                     TikZ.Property("execute at end node", "\$") ])
  end
  TikZ.Picture(mor.node; props=props)
end

function mor_tikz(f::MorExpr, name::String, style::Dict)::MorTikZ
  mor_tikz(f, name, style, Val{head(f)})
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:gen}})
  dom_ports = box_anchors(dom(f), name, style, dir="west")
  codom_ports = box_anchors(codom(f), name, style, dir="east")
  height = box_size(max(length(dom_ports), length(codom_ports)), style)
  props = [
    TikZ.Property("generator"),
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(name; content=string(first(args(f))), props=props)
  MorTikZ(node, dom_ports, codom_ports)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:id}})
  ports = box_anchors(dom(f), name, style, dir="center")
  height = box_size(length(ports), style)
  props = [
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(name; props=props)
  MorTikZ(node, ports, ports)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:compose}})
  compose_sep = style[:compose_sep]
  mors = [ mor_tikz(g, "$name$i", style) for (i,g) in enumerate(args(f)) ]
  stmts = TikZ.Statement[ mors[1].node ]
  for i = 2:length(mors)
    push!(mors[i].node.props,
          TikZ.Property("right=$(compose_sep)em of $name$(i-1))"))
    push!(stmts, mors[i].node)
    for j = 1:length(mors[i].dom)
      edge = TikZ.Edge(mors[i-1].codom[j].anchor, mors[i].dom[j].anchor;
                       props=[TikZ.Property("postaction","{decorate}")],
                       op=TikZ.PathOperation("to"))
      push!(stmts, edge)
    end
  end

  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=TikZ.Picture(stmts...), props=props)
  MorTikZ(node, first(mors).dom, last(mors).codom)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:otimes}})
  product_sep = style[:product_sep]
  mors = []
  for (i,g) in enumerate(args(f))
    mor = mor_tikz(g, "$name$i", style)
    if i > 1
      push!(mor.node.props,
            TikZ.Property("below=$(product_sep)em of $name$(i-1)"))
      end
    push!(mors, mor)
  end
  stmts = TikZ.Statement[ mor.node for mor in mors ]

  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=TikZ.Picture(stmts...), props=props)
  dom = vcat([ mor.dom for mor in mors]...)
  codom = vcat([ mor.codom for mor in mors]...)
  MorTikZ(node, dom, codom)
end

""" Compute the size of a box from the number of its ports.

We use the unique formula consistent with the monoidal product, meaning that
the size of a product of generator boxes depends only on the total number of
ports, not the number of generators.
"""
function box_size(ports::Int, style::Dict)::Number
  m = max(1, ports)
  m * style[:box_size] + (m-1) * style[:product_sep]
end

""" Compute the locations of ports on a box.

These anchors are consistent with the monoidal product (see `box_size`).
"""
function box_anchors(A::ObExpr, name::String, style::Dict;
                     dir::String="center")::Vector{PortTikZ}
  box_size, product_sep = style[:box_size], style[:product_sep]
  @match A begin
    ObExpr(:unit, _) => []
    ObExpr(:gen, syms) => [ PortTikZ("$name.$dir", string(first(syms))) ]
    ObExpr(:otimes, gens) => begin
      @assert all(head(B) == :gen for B in gens)
      ports = []
      m = length(gens)
      start = (m*box_size + (m-1)*product_sep) / 2
      for (i,B) in enumerate(gens)
        offset = box_size/2 + (i-1)*(box_size+product_sep)
        anchor = "\$($name.$dir)+(0,$(start-offset)em)\$"
        push!(ports, PortTikZ(anchor, string(first(args(B)))))
      end
      ports
    end
  end
end

end

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
                      compose_sep::Number=2, tensor_sep::Number=1)::TikZ.Picture
  # Draw input and output arrows by adding identities on either side of f. 
  f_ext = compose(id(dom(f)), f, id(codom(f)))
  
  mor = mor_tikz(f_ext, "n"; compose_sep=compose_sep, tensor_sep=tensor_sep)
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("decoration", 
                  "{markings, mark=at position 0.5 with {\\arrow{stealth}}}"),
    TikZ.Property("font", "{\\fontsize{$font_size}{$(format(1.2*font_size))}}"),
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

function mor_tikz(f::MorExpr, name::String; kwargs...)::MorTikZ
  mor_tikz(f, name, Val{head(f)}; kwargs...)
end

function mor_tikz(f::MorExpr, name::String, ::Type{Val{:gen}}; kwargs...)
  dom_ports = ports_tikz(dom(f), name, "west")
  codom_ports = ports_tikz(codom(f), name, "east")
  height = 2 * max(1, length(dom_ports), length(codom_ports))
  props = [
    TikZ.Property("generator"),
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(name; content=string(first(args(f))), props=props)
  MorTikZ(node, dom_ports, codom_ports)
end

function mor_tikz(f::MorExpr, name::String, ::Type{Val{:id}}; kwargs...)
  ports = ports_tikz(dom(f), name, "center")
  height = 2 * max(1, length(ports))
  props = [
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(name; props=props)
  MorTikZ(node, ports, ports)
end

function mor_tikz(f::MorExpr, name::String, ::Type{Val{:compose}}; kwargs...)
  kwargs = Dict(kwargs)
  compose_sep = kwargs[:compose_sep]

  mors = [ mor_tikz(g, "$name$i"; kwargs...) for (i,g) in enumerate(args(f)) ]
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

function mor_tikz(f::MorExpr, name::String, ::Type{Val{:otimes}}; kwargs...)
  kwargs = Dict(kwargs)
  tensor_sep = kwargs[:tensor_sep]

  mors = []
  for (i,g) in enumerate(args(f))
    mor = mor_tikz(g, "$name$i"; kwargs...)
    if i > 1
      push!(mor.node.props,
            TikZ.Property("below=$(tensor_sep)em of $name$(i-1)"))
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

function ports_tikz(A::ObExpr, name::String, dir::String)::Vector{PortTikZ}
  @match A begin
    ObExpr(:unit, _) => []
    ObExpr(:gen, syms) => [ PortTikZ("$name.$dir", string(first(syms))) ]
    ObExpr(:otimes, gens) => begin
      @assert all(head(B) == :gen for B in gens)
      m = length(gens)
      dir = dir == "center" ? "" : " $dir"
      ports = []
      for (i,B) in enumerate(gens)
        frac = @sprintf "%.3f" (i / (m+1))
        anchor = "\$($name.north$dir)!$(frac)!($name.south$dir)\$"
        push!(ports, PortTikZ(anchor, string(first(args(B)))))
      end
      ports
    end
  end
end

end

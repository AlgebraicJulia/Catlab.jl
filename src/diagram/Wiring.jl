""" Draw wiring diagrams (aka string diagrams) in various formats.
"""
module Wiring
export diagram_tikz

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

""" TODO

Warning: Since our implementation uses the `remember picture` option, LaTeX must
be *twice* to fully render the picture. See (TikZ Manual, Sec 17.13).
"""
function diagram_tikz(f::MorExpr; math_mode::Bool=true, kwargs...)::TikZ.Picture
  #f_in = otimes([ id(A) for A in dom(f) ]...)
  #f_out = otimes([ id(B) for B in codom(f) ]...)
  #mor = mor_tikz(compose(f_in, f, f_out); kwargs...)
  mor = mor_tikz(f; kwargs...)
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("decoration", "{markings, mark=at position 0.5 with {\\arrow{>}}}"),
    TikZ.Property("every to/.style", "{out=0,in=180}")
  ]
  if math_mode
    append!(props, [ TikZ.Property("execute at begin node", "\$"),
                     TikZ.Property("execute at end node", "\$") ])
  end
  TikZ.Picture(mor.node; props=props)
end

function mor_tikz(f::MorExpr; prefix::String="n", kwargs...)::MorTikZ
  mor_tikz(f, Val{head(f)}; prefix=prefix, kwargs...)
end

function mor_tikz(f::MorExpr, ::Type{Val{:gen}}; prefix::String="", kwargs...)
  dom_ports = ports_tikz(dom(f), prefix, "west")
  codom_ports = ports_tikz(codom(f), prefix, "east")
  height = 2 * max(1, length(dom_ports), length(codom_ports))
  props = [
    TikZ.Property("draw"),
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(prefix; content=string(first(args(f))), props=props)
  MorTikZ(node, dom_ports, codom_ports)
end

function mor_tikz(f::MorExpr, ::Type{Val{:id}}; prefix::String="", kwargs...)
  ports = ports_tikz(dom(f), prefix, "center")
  height = 2 * max(1, length(ports))
  props = [
    TikZ.Property("minimum height", "$(height)em")
  ]
  node = TikZ.Node(prefix; props=props)
  MorTikZ(node, ports, ports)
end

function mor_tikz(f::MorExpr, ::Type{Val{:compose}}; prefix::String="", kwargs...)
  kwargs = Dict(kwargs)
  compose_sep = get(kwargs, :compose_sep, "2em")
  name(i) = "$(prefix)$i"

  mors = [ mor_tikz(g; prefix=name(i), kwargs...) for (i,g) in enumerate(args(f)) ]
  stmts = TikZ.Statement[ mors[1].node ]
  for i = 2:length(mors)
    push!(mors[i].node.props,
          TikZ.Property("right=$compose_sep of $(name(i-1))"))
    push!(stmts, mors[i].node)
    for j = 1:length(mors[i].dom)
      edge = TikZ.Edge(mors[i-1].codom[j].anchor, mors[i].dom[j].anchor;
                       props=[TikZ.Property("postaction","{decorate}")],
                       op=TikZ.PathOperation("to"))
      push!(stmts, edge)
    end
  end

  node = TikZ.Node(prefix; content=TikZ.Picture(stmts...))
  MorTikZ(node, first(mors).dom, last(mors).codom)
end

function mor_tikz(f::MorExpr, ::Type{Val{:otimes}}; prefix::String="", kwargs...)
  kwargs = Dict(kwargs)
  tensor_sep = get(kwargs, :tensor_sep, "1em")
  name(i) = "$(prefix)$i"

  mors = []
  for (i,g) in enumerate(args(f))
    mor = mor_tikz(g; prefix=name(i), kwargs...)
    if i > 1
      push!(mor.node.props,
            TikZ.Property("below=$tensor_sep of $(name(i-1))"))
      end
    push!(mors, mor)
  end
  stmts = TikZ.Statement[ mor.node for mor in mors ]

  node = TikZ.Node(prefix; content=TikZ.Picture(stmts...))
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
      ports = []
      for (i,B) in enumerate(gens)
        frac = @sprintf "%.3f" (i / (m+1))
        anchor = "\$($name.north $dir)!$(frac)!($name.south $dir)\$"
        push!(ports, PortTikZ(anchor, string(first(args(B)))))
      end
      ports
    end
  end
end

end

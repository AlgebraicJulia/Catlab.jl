""" Draw wiring diagrams (aka string diagrams) in various formats.
"""
module Wiring
export diagram_tikz

import Formatting: format
using Match

import ...Syntax
import ...Syntax: ObExpr, MorExpr, dom, codom, head, args, compose, id
import ..TikZ

# TikZ
######

immutable PortTikZ
  ob::ObExpr
  anchor::AbstractString
  angle::Integer
  label::Bool
  PortTikZ(ob::ObExpr, anchor::AbstractString;
           angle::Integer=0, label::Bool=true) = new(ob, anchor, angle, label)
end

immutable MorTikZ
  mor::MorExpr
  node::TikZ.Node
  dom::Vector{PortTikZ}
  codom::Vector{PortTikZ}
end

""" Draw a wiring diagram in TikZ for the given formula.

The diagram is constructed recursively, mirroring the structure of the formula.
This is achieved by nesting TikZ pictures in TikZ nodes recursively--a feature
not officially supported by TikZ but that is nonetheless in widespread use.

Warning: Since our implementation uses the `remember picture` option, LaTeX must
be run *twice* to fully render the picture. See (TikZ Manual, Sec 17.13).
"""
function diagram_tikz(f::MorExpr;
    font_size::Number=12, line_width::String="0.4pt", math_mode::Bool=true,
    arrowtip::String="", labels::Bool=true,
    box_padding::String="0.333em", box_size::Number=2,
    compose_sep::Number=2, product_sep::Number=0.5)::TikZ.Picture
  # Parse arguments.
  style = Dict(:arrowtip => !isempty(arrowtip), :labels => labels,
               :box_size => box_size, :compose_sep => compose_sep,
               :product_sep => product_sep)
  
  # Draw input and output arrows by adding identities on either side of f. 
  f_ext = f
  if head(f) == :id
    f_ext = compose(id(dom(f)), f_ext)
  else
    if head(dom(f)) != :unit
      f_ext = compose(id(dom(f)), f_ext)
    end
    if head(codom(f)) != :unit
      f_ext = compose(f_ext, id(codom(f)))
    end
  end
  
  # Create node for extended morphism.
  mor = mor_tikz(f_ext, "n", style)
  
  # Create picture with this single node.
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("font", 
                  "{\\fontsize{$(format(font_size))}{$(format(1.2*font_size))}}"),
    TikZ.Property("morphism node/.style",
                  "{draw,solid,inner sep=$box_padding}"),
    TikZ.Property("monoid node/.style",
                  "{draw,fill,circle,minimum size=0.333em}"),
    TikZ.Property("container/.style", "{inner sep=0}"),
    TikZ.Property("every path/.style",
                  "{solid, line width=$line_width}"),
  ]
  if !isempty(arrowtip)
    decoration = "{markings, mark=at position 0.5 with {\\arrow{$arrowtip}}}"
    push!(props, TikZ.Property("decoration", decoration))
  end
  if math_mode
    append!(props, [ TikZ.Property("execute at begin node", "\$"),
                     TikZ.Property("execute at end node", "\$") ])
  end
  TikZ.Picture(mor.node; props=props)
end

""" Create a TikZ node representing a morphism.
"""
function mor_tikz(f::MorExpr, name::String, style::Dict)::MorTikZ
  mor_tikz(f, name, style, Val{head(f)})
end

# Category

""" Create a TikZ node representing a generator morphism.

The node content is a nested TikZ picture that typically contains a visible
node. Nesting pictures even at this level may seem crazy, but it's the only way
I know to get a bounding box on the inner node, regardless of its shape,
*before* it's rendered. In fact, this is the same problem that forces us to use
nested pictures in the first place.
"""
function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:gen}})
  # TODO: For maximum flexibility, we could defer the calculation of the anchor
  # locations to the renderer. Presently we assume that the node is sufficiently
  # "box-like" for the default anchors to make sense.
  dom_ports = box_anchors(dom(f), name, style, dir="west", angle=180)
  codom_ports = box_anchors(codom(f), name, style, dir="east", angle=0)
  size = box_size(max(length(dom_ports), length(codom_ports)), style)
  
  content = box_renderer_trapezium(f, "$name box", size)
  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=content, props=props)
  MorTikZ(f, node, dom_ports, codom_ports)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:id}})
  dom_ports = box_anchors(dom(f), name, style, dir="center", angle=180)
  codom_ports = box_anchors(codom(f), name, style, dir="center", angle=0)
  height = box_size(length(dom_ports), style)
  props = [ TikZ.Property("minimum height", "$(height)em") ]
  node = TikZ.Node(name; props=props)
  MorTikZ(f, node, dom_ports, codom_ports)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:compose}})
  compose_sep = style[:compose_sep]
  edge_props = style[:arrowtip] ?
    [ TikZ.Property("postaction", "{decorate}") ] : []
  edge_node_props = [
    TikZ.Property("above", "0.25em"),
    TikZ.Property("midway")
  ]
  
  mors = [ mor_tikz(g, "$name$i", style) for (i,g) in enumerate(args(f)) ]
  stmts = TikZ.Statement[ mors[1].node ]
  for i = 2:length(mors)
    push!(mors[i].node.props,
          TikZ.Property("right=$(compose_sep)em of $name$(i-1))"))
    push!(stmts, mors[i].node)
    for j = 1:length(mors[i].dom)
      src_port = mors[i-1].codom[j]
      tgt_port = mors[i].dom[j]
      
      # Create edge node for label.
      if (style[:labels] && src_port.label && tgt_port.label)
        node = TikZ.EdgeNode(content=wire_label(tgt_port.ob),
                             props=edge_node_props)
      else
        node = Nullable()
      end
      
      # Create path operation and draw edge.
      op = TikZ.PathOperation("to"; props=[
        TikZ.Property("out", string(src_port.angle)),
        TikZ.Property("in", string(tgt_port.angle)),
      ])
      edge = TikZ.Edge(src_port.anchor, tgt_port.anchor;
                       op=op, props=edge_props, node=node)
      push!(stmts, edge)
    end
  end

  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=TikZ.Picture(stmts...), props=props)
  MorTikZ(f, node, first(mors).dom, last(mors).codom)
end

# Monoidal category

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
  MorTikZ(f, node, dom, codom)
end

# Symmetric monoidal category

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:braid}})
  A, B = args(f)[1], args(f)[2]
  center = "$name.center"
  dom = [ PortTikZ(A, center, angle=135), PortTikZ(B, center, angle=225) ]
  codom = [ PortTikZ(B, center, angle=45), PortTikZ(A, center, angle=315) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2,style))em")
  ]
  node = TikZ.Node(name; props=props)
  MorTikZ(f, node, dom, codom)
end

# Internal (co)monoid

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:copy}})
  A = Syntax.dom(f)
  dom = [ PortTikZ(A, "$name.west", angle=180) ]
  codom = [ PortTikZ(A, "$name.north", angle=90, label=false),
            PortTikZ(A, "$name.south", angle=270, label=false) ]
  node = TikZ.Node(name; props=[TikZ.Property("monoid node")])
  MorTikZ(f, node, dom, codom)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:merge}})
  A = Syntax.codom(f)
  dom = [ PortTikZ(A, "$name.north", angle=90, label=false),
          PortTikZ(A, "$name.south", angle=270, label=false) ]
  codom = [ PortTikZ(A, "$name.east", angle=0) ]
  node = TikZ.Node(name; props=[TikZ.Property("monoid node")])
  MorTikZ(f, node, dom, codom)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:create}})
  ports = [ PortTikZ(codom(f), "$name.east", angle=0) ]
  node = TikZ.Node(name; props=[TikZ.Property("monoid node")])
  MorTikZ(f, node, [], ports)
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:delete}})
  ports = [ PortTikZ(dom(f), "$name.west", angle=180) ]
  node = TikZ.Node(name; props=[TikZ.Property("monoid node")])
  MorTikZ(f, node, ports, [])
end

# Compact closed category

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:eval}})
  ports = [ PortTikZ(args(dom(f))[1], "$name.center", angle=90, label=false),
            PortTikZ(args(dom(f))[2], "$name.center", angle=270, label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2,style))em")
  ]
  node = TikZ.Node(name; props=props)
  MorTikZ(f, node, ports, [])
end

function mor_tikz(f::MorExpr, name::String, style::Dict, ::Type{Val{:coeval}})
  ports = [ PortTikZ(args(codom(f))[1], "$name.center", angle=90, label=false),
            PortTikZ(args(codom(f))[2], "$name.center", angle=270, label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2,style))em")
  ]
  node = TikZ.Node(name; props=props)
  MorTikZ(f, node, [], ports)
end

# Helper functions

""" The "default" renderer for a generator box.

Draws a rectangle with rounded corners.
"""
function box_renderer_rectangle(gen::MorExpr, name::String,
                                size::Number)::TikZ.Picture
  props = [
    TikZ.Property("morphism node"),
    TikZ.Property("rectangle"),
    TikZ.Property("rounded corners"),
    TikZ.Property("minimum height", "$(size)em")
  ]
  node = TikZ.Node(name; content=box_label(gen), props=props)
  TikZ.Picture(node)
end

""" Draws a rotated trapezium with rounded corners.
"""
function box_renderer_trapezium(gen::MorExpr, name::String,
                                size::Number)::TikZ.Picture
  props = [
    TikZ.Property("morphism node"),
    TikZ.Property("trapezium"),
    TikZ.Property("trapezium angle", "80"),
    TikZ.Property("trapezium stretches body"),
    TikZ.Property("shape border rotate", "270"),
    TikZ.Property("rounded corners"),
    # Actually the height because of rotation.
    TikZ.Property("minimum width", "$(size)em")
  ]
  node = TikZ.Node(name; content=box_label(gen), props=props)
  TikZ.Picture(node)
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
                     dir::String="center", kwargs...)::Vector{PortTikZ}
  box_size, product_sep = style[:box_size], style[:product_sep]
  @match A begin
    ObExpr(:unit, _) => []
    ObExpr(:otimes, gens) => begin
      ports = []
      m = length(gens)
      start = (m*box_size + (m-1)*product_sep) / 2
      for (i,B) in enumerate(gens)
        offset = box_size/2 + (i-1)*(box_size+product_sep)
        anchor = "\$($name.$dir)+(0,$(start-offset)em)\$"
        push!(ports, PortTikZ(B, anchor; kwargs...))
      end
      ports
    end
    _ => [ PortTikZ(A, "$name.$dir"; kwargs...) ]
  end
end

""" Get label for a box (a morphism).
"""
box_label(f::MorExpr) = box_label(f, Val{head(f)})
box_label(f::MorExpr, ::Type{Val{:gen}}) = string(first(args(f)))

""" Get label for a wire (an object).
"""
wire_label(A::ObExpr) = wire_label(A, Val{head(A)})
wire_label(A::ObExpr, ::Type{Val{:gen}}) = string(first(args(A)))
wire_label(A::ObExpr, ::Type{Val{:dual}}) = wire_label(first(args(A)))

end

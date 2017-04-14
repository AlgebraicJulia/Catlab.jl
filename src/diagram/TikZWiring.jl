""" Draw wiring diagrams (aka string diagrams) in various formats.
"""
module TikZWiring
export WireTikZ, WiresTikZ, PortTikZ, BoxTikZ,
  wiring_diagram, wires, box, sequence, parallel,
  rect, trapezium, lines, crossing, junction_circle, cup, cap

import Formatting: format
using Match

import ...Doctrine: ObExpr, HomExpr, dom, codom, head, args, compose, id
import ..TikZ

# Data types
############

immutable WireTikZ
  label::String
  reverse::Bool
  WireTikZ(label::String; reverse::Bool=false) = new(label, reverse)
end

""" Object in a TikZ wiring diagram.
"""
typealias WiresTikZ Vector{WireTikZ}

immutable PortTikZ
  wire::WireTikZ
  anchor::String
  angle::Int
  show_label::Bool
  PortTikZ(wire::WireTikZ, anchor::String; angle::Int=0, show_label::Bool=true) =
    new(wire, anchor, angle, show_label)
end

""" Morphism in a TikZ wiring diagram.
"""
immutable BoxTikZ
  node::TikZ.Node
  inputs::Vector{PortTikZ}
  outputs::Vector{PortTikZ}
end
dom(box::BoxTikZ)::WiresTikZ = [ port.label for port in box.inputs ]
codom(box::BoxTikZ)::WiresTikZ  = [ port.label for port in box.outputs ]

# Wiring diagrams
#################

""" Draw a wiring diagram in TikZ for the given morphism expression.

The diagram is constructed recursively, mirroring the structure of the formula.
This is achieved by nesting TikZ pictures in TikZ nodes recursively--a feature
not officially supported by TikZ but that is nonetheless in widespread use.

Warning: Since our implementation uses the `remember picture` option, LaTeX must
be run at least *twice* to fully render the picture. See (TikZ Manual,
Sec 17.13).
"""
function wiring_diagram(f::HomExpr;
    font_size::Number=12, line_width::String="0.4pt", math_mode::Bool=true,
    arrowtip::String="", labels::Bool=true,
    box_size::Number=2, box_style::Dict=Dict(),
    sequence_sep::Number=2, parallel_sep::Number=0.5)::TikZ.Picture
  # Parse arguments.
  # XXX: Storing the style parameters as a global variable is bad practice, but
  # passing them around is really inconvenient. Is there a better approach?
  global style = Dict(
    :arrowtip => !isempty(arrowtip), :labels => labels,
    :box_size => box_size, :box_style => box_style,
    :sequence_sep => sequence_sep, :parallel_sep => parallel_sep,
  )
  
  # Draw input and output arrows by adding identities on either side of f. 
  f_ext = f
  if head(f) == :id
    f_ext = compose(id(dom(f)), f_ext)
  else
    if head(dom(f)) != :munit
      f_ext = compose(id(dom(f)), f_ext)
    end
    if head(codom(f)) != :munit
      f_ext = compose(f_ext, id(codom(f)))
    end
  end
  
  # Create node for extended morphism.
  box_tikz = box("n", f_ext)
  
  # Create picture with this single node.
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("font", 
                  "{\\fontsize{$(format(font_size))}{$(format(1.2*font_size))}}"),
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
  TikZ.Picture(box_tikz.node; props=props)
end

""" Create wires for an object expression.
"""
function wires(A::ObExpr)::WiresTikZ end

""" Create box for a morphism expression.
"""
function box(name::String, f::HomExpr)::BoxTikZ end

# Elements of wiring diagrams
#############################

""" A rectangle, the default style for generators.
"""
function rect(name::String, content::String, dom::WiresTikZ, codom::WiresTikZ;
              padding::String="0.333em", rounded::Bool=true)::BoxTikZ
  dom_ports = box_ports(dom, name, dir="west", angle=180)
  codom_ports = box_ports(codom, name, dir="east", angle=0)
  size = box_size(max(length(dom_ports), length(codom_ports)))
  
  box_style = style[:box_style]
  props = [
    TikZ.Property("draw"),
    TikZ.Property("solid"),
    TikZ.Property("inner sep", get(box_style, :padding, padding)),
    TikZ.Property("rectangle"),
    TikZ.Property(get(box_style, :rounded, rounded) ?
                  "rounded corners" : "sharp corners"),
    TikZ.Property("minimum height", "$(size)em"),
  ]
  node = TikZ.Node(name; content=content, props=props)
  BoxTikZ(node, dom_ports, codom_ports)
end
function rect(name::String, f::HomExpr{:generator}; kw...)::BoxTikZ
  rect(name, string(first(f)), wires(dom(f)), wires(codom(f)); kw...)
end

""" A trapezium node, the default style for generators in dagger categories.

The node content is a nested TikZ picture that contains a single visible node.
Nesting pictures even at this level may seem crazy, but it's the only way I know
to get a bounding box on the inner node, regardless of its shape, *before* it's
rendered.
"""
function trapezium(name::String, content::String, dom::WiresTikZ, codom::WiresTikZ;
                   padding::String="0.333em", rounded::Bool=true,
                   angle::Int=80, reverse::Bool=false)::BoxTikZ
  dom_ports = box_ports(dom, name, dir="west", angle=180)
  codom_ports = box_ports(codom, name, dir="east", angle=0)
  size = box_size(max(length(dom_ports), length(codom_ports)))
  
  box_style = style[:box_style]
  props = [
    TikZ.Property("draw"),
    TikZ.Property("solid"),
    TikZ.Property("inner sep", get(box_style, :padding, padding)),
    TikZ.Property("trapezium"),
    TikZ.Property("trapezium angle", string(get(box_style, :angle, angle))),
    TikZ.Property("trapezium stretches body"),
    TikZ.Property("shape border rotate", reverse ? "90" : "270"),
    TikZ.Property(get(box_style, :rounded, rounded) ?
                  "rounded corners" : "sharp corners"),
    # Actually the height because of rotation.
    TikZ.Property("minimum width", "$(size)em"),
  ]
  node = TikZ.Node("$name box"; content=content, props=props)
  picture = TikZ.Picture(node)
  
  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=picture, props=props)
  BoxTikZ(node, dom_ports, codom_ports)
end
function trapezium(name::String, f::HomExpr{:generator}; kw...)::BoxTikZ
  trapezium(name, string(first(f)), wires(dom(f)), wires(codom(f)); kw...)
end

""" Straight lines, used to draw identity morphisms.
"""
function lines(name::String, wires::WiresTikZ)::BoxTikZ
  dom_ports = box_ports(wires, name, dir="center", angle=180)
  codom_ports = box_ports(wires, name, dir="center", angle=0)
  height = box_size(length(wires))
  props = [ TikZ.Property("minimum height", "$(height)em") ]
  node = TikZ.Node(name; props=props)
  BoxTikZ(node, dom_ports, codom_ports)
end
lines(name::String, A::ObExpr) = lines(name, wires(A))

""" Boxes in sequence, used to draw compositions.
"""
function sequence(name::String, homs::Vector)::BoxTikZ
  sequence_sep = style[:sequence_sep]
  edge_props = style[:arrowtip] ?
    [ TikZ.Property("postaction", "{decorate}") ] : []
  edge_node_props = [
    TikZ.Property("above", "0.25em"),
    TikZ.Property("midway")
  ]
  
  mors = [ box("$name$i", g) for (i,g) in enumerate(homs) ]
  stmts = TikZ.Statement[ mors[1].node ]
  for i = 2:length(mors)
    push!(mors[i].node.props,
          TikZ.Property("right=$(sequence_sep)em of $name$(i-1))"))
    push!(stmts, mors[i].node)
    for j = 1:length(mors[i].inputs)
      src_port = mors[i-1].outputs[j]
      tgt_port = mors[i].inputs[j]
      
      # Create edge node for label.
      wire = tgt_port.wire # == src_port.wire
      if (style[:labels] && src_port.show_label && tgt_port.show_label)
        node = TikZ.EdgeNode(content=wire.label, props=edge_node_props)
      else
        node = Nullable()
      end
      
      # Create path operation and draw edge.
      if wire.reverse
        src_port, tgt_port = tgt_port, src_port
      end
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
  BoxTikZ(node, first(mors).inputs, last(mors).outputs)
end

""" Boxes in parallel, used to draw monoidal products.
"""
function parallel(name::String, homs::Vector)::BoxTikZ
  parallel_sep = style[:parallel_sep]
  
  mors = []
  for (i,g) in enumerate(homs)
    mor = box("$name$i", g)
    if i > 1
      push!(mor.node.props,
            TikZ.Property("below=$(parallel_sep)em of $name$(i-1)"))
    end
    push!(mors, mor)
  end
  stmts = TikZ.Statement[ mor.node for mor in mors ]

  props = [ TikZ.Property("container") ]
  node = TikZ.Node(name; content=TikZ.Picture(stmts...), props=props)
  inputs = vcat([ mor.inputs for mor in mors]...)
  outputs = vcat([ mor.outputs for mor in mors]...)
  BoxTikZ(node, inputs, outputs)
end

""" Cross two wires.

Used to draw braid morphisms in symmatric monoidal categories.
""" 
function crossing(name::String, wire1::WireTikZ, wire2::WireTikZ)
  dom = [ PortTikZ(wire1, "$name.center", angle=135),
          PortTikZ(wire2, "$name.center", angle=225) ]
  codom = [ PortTikZ(wire2, "$name.center", angle=45),
            PortTikZ(wire1, "$name.center", angle=315) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  BoxTikZ(node, dom, codom)
end
crossing(name::String, A::ObExpr) = crossing(name, wires(A)...)

""" A junction of wires drawn as a circle.

Used to morphisms in internal monoids and comonoids.

Implemented using a small, visible node for the point and a big, invisible node
as a spacer. FIXME: Is there a more elegant way to achieve the desired margin?
"""
function junction_circle(name::String, wires_in::WiresTikZ, wires_out::WiresTikZ;
                         fill::Bool=true)
  m = max(length(wires_in), length(wires_out))
  @assert m <= 2
  dom = @match length(wires_in) begin
    0 => []
    1 => [ PortTikZ(wires_in[1], "$name point.west", angle=180) ]
    2 => [ PortTikZ(wires_in[1], "$name point.north", angle=90, show_label=false),
           PortTikZ(wires_in[2], "$name point.south", angle=270, show_label=false) ]
  end
  codom = @match length(wires_out) begin
    0 => []
    1 => [ PortTikZ(wires_out[1], "$name point.east", angle=0) ]
    2 => [ PortTikZ(wires_out[1], "$name point.north", angle=90, show_label=false),
           PortTikZ(wires_out[2], "$name point.south", angle=270, show_label=false) ]
  end
  
  pic = TikZ.Picture(
    TikZ.Node("$name box"; props=[
      TikZ.Property("minimum height", "$(box_size(m))em"),
    ]),
    TikZ.Node("$name point"; props=[
      TikZ.Property("draw"),
      TikZ.Property(fill ? "fill" : "solid"),
      TikZ.Property("circle"),
      TikZ.Property("minimum size", "0.333em"),
      TikZ.Property("above", "0 of $name box.center"),
      TikZ.Property("anchor", "center"),
    ]),
  )
  node = TikZ.Node(name; content=pic, props=[TikZ.Property("container")])
  BoxTikZ(node, dom, codom)
end
function junction_circle(name::String, dom::ObExpr, codom::ObExpr; kw...)
  junction_circle(name, wires(dom), wires(codom); kw...)
end
function junction_circle(name::String, f::HomExpr; kw...)
  junction_circle(name, dom(f), codom(f); kw...)
end

""" A cup.

Used to draw evaluation morphisms in compact closed categories.
"""
function cup(name::String, wire1::WireTikZ, wire2::WireTikZ)
  ports = [ PortTikZ(wire1, "$name.center", angle=90, show_label=false),
            PortTikZ(wire2, "$name.center", angle=270, show_label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  BoxTikZ(node, ports, [])
end
cup(name::String, A::ObExpr) = cup(name, wires(A)...)

""" A cap.

Used to draw coevaluation morphisms in compact closed categories.
"""
function cap(name::String, wire1::WireTikZ, wire2::WireTikZ)
  ports = [ PortTikZ(wire1, "$name.center", angle=90, show_label=false),
            PortTikZ(wire2, "$name.center", angle=270, show_label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  BoxTikZ(node, [], ports)
end
cap(name::String, A::ObExpr) = cap(name, wires(A)...)

# Helper functions
##################

""" Compute the size of a box from the number of its ports.

We use the unique formula consistent with the monoidal product, meaning that
the size of a product of generator boxes depends only on the total number of
ports, not the number of generators.
"""
function box_size(ports::Int)::Number
  m = max(1, ports)
  m * style[:box_size] + (m-1) * style[:parallel_sep]
end

""" Create ports for a rectangular box.

This mainly involves computing the locations of anchors. The anchors are
consistent with the monoidal product (see `box_size`).
"""
function box_ports(wires::WiresTikZ, name::String;
                   dir::String="center", kwargs...)::Vector{PortTikZ}
  box_size, parallel_sep = style[:box_size], style[:parallel_sep]
  m = length(wires)
  if m == 0
    return []
  elseif m == 1
    return [ PortTikZ(wires[1], "$name.$dir"; kwargs...) ]
  end
  
  result = []
  start = (m*box_size + (m-1)*parallel_sep) / 2
  for (i,wire) in enumerate(wires)
    offset = box_size/2 + (i-1)*(box_size+parallel_sep)
    anchor = "\$($name.$dir)+(0,$(start-offset)em)\$"
    push!(result, PortTikZ(wire, anchor; kwargs...))
  end
  return result
end

# Defaults
##########

# These methods are reasonable to define for the base expression types since
# they will rarely be changed.

wires(A::ObExpr{:generator}) = [ WireTikZ(string(first(A))) ]
wires(A::ObExpr{:munit}) = WireTikZ[]
wires(A::ObExpr{:otimes}) = vcat(map(wires, args(A))...)

box(name::String, f::HomExpr{:id}) = lines(name, dom(f))
box(name::String, f::HomExpr{:compose}) = sequence(name, args(f))
box(name::String, f::HomExpr{:otimes}) = parallel(name, args(f))
box(name::String, f::HomExpr{:braid}) = crossing(name, dom(f))

""" Default renderers for specific syntax systems.
"""
module Defaults
  export box, wires
  
  using ..TikZWiring
  import ..TikZWiring: box, wires
  using CompCat.Doctrine
  using CompCat.Syntax
  
  generator(expr::BaseExpr)::BaseExpr{:generator} = first(expr)
  
  # Category
  box(name::String, f::FreeCategory.Hom{:generator}) = rect(name, f)
  
  # Dagger category
  # Assumes that daggers are fully distributed (as in this syntax system).
  Syntax = FreeDaggerCategory
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    string(first(generator(f))), wires(dom(f)), wires(codom(f)); reverse=true)

  # Symmetric monoidal category
  Syntax = FreeSymmetricMonoidalCategory
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)

  # (Co)cartesian category
  Syntax = FreeCartesianCategory
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)
  box(name::String, f::Syntax.Hom{:mcopy}) = junction_circle(name, f)
  box(name::String, f::Syntax.Hom{:delete}) = junction_circle(name, f)
  
  Syntax = FreeCocartesianCategory
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)
  box(name::String, f::Syntax.Hom{:mmerge}) = junction_circle(name, f)
  box(name::String, f::Syntax.Hom{:create}) = junction_circle(name, f)
  
  # Biproduct category
  Syntax = FreeBiproductCategory
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)
  box(name::String, f::Syntax.Hom{:mcopy}) = junction_circle(name, f)
  box(name::String, f::Syntax.Hom{:delete}) = junction_circle(name, f)
  box(name::String, f::Syntax.Hom{:mmerge}) = junction_circle(name, f)
  box(name::String, f::Syntax.Hom{:create}) = junction_circle(name, f)
  
  # Compact closed category
  # Assumes that duals are fully distributed (as in this syntax system).
  Syntax = FreeCompactClosedCategory
  wires(A::Syntax.Ob{:dual}) = [ WireTikZ(string(first(generator(A))); reverse=true) ]
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)
  box(name::String, f::Syntax.Hom{:ev}) = cup(name, dom(f))
  box(name::String, f::Syntax.Hom{:coev}) = cap(name, codom(f))
  
  # Bicategory of relations
  Syntax = FreeBicategoryRelations
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    string(first(generator(f))), wires(dom(f)), wires(codom(f)); reverse=true)
  box(name::String, f::Syntax.Hom{:ev}) = cup(name, dom(f))
  box(name::String, f::Syntax.Hom{:coev}) = cap(name, codom(f))
  box(name::String, f::Syntax.Hom{:mcopy}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:delete}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:mmerge}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:create}) = junction_circle(name, f; fill=false)
  
  Syntax = FreeAbelianBicategoryRelations
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    string(first(generator(f))), wires(dom(f)), wires(codom(f)); reverse=true)
  box(name::String, f::Syntax.Hom{:ev}) = cup(name, dom(f))
  box(name::String, f::Syntax.Hom{:coev}) = cap(name, codom(f))
  box(name::String, f::Syntax.Hom{:mcopy}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:delete}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:mmerge}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:create}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:plus}) = junction_circle(name, f; fill=true)
  box(name::String, f::Syntax.Hom{:zero}) = junction_circle(name, f; fill=true)
  box(name::String, f::Syntax.Hom{:coplus}) = junction_circle(name, f; fill=true)
  box(name::String, f::Syntax.Hom{:cozero}) = junction_circle(name, f; fill=true)
end

end

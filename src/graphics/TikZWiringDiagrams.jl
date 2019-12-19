""" Draw wiring diagrams using TikZ.
"""
module TikZWiringDiagrams
export to_tikz

using Match

using ...Doctrines: ObExpr, HomExpr, dom, codom, head, args, compose, id
using ...Syntax: GATExpr, show_latex
using ...WiringDiagrams
import ..TikZ

# Data types
############

""" A wire (edge) in a TikZ wiring diagram.
"""
struct Wire
  label::String
  reverse::Bool
  Wire(label::String; reverse::Bool=false) = new(label, reverse)
end

""" A bundle of wires in a TikZ wiring diagram.

A graphical representation of an object.
"""
const Wires = Vector{Wire}

""" A port on a box in a TikZ wiring diagram.
"""
struct Port
  wire::Wire
  anchor::String
  angle::Int
  show_label::Bool
  Port(wire::Wire, anchor::String; angle::Int=0, show_label::Bool=true) =
    new(wire, anchor, angle, show_label)
end

""" A box in a TikZ wiring diagram.

A `Box` is a graphical representation of a morphism, and need not be rendered
as a geometric box (rectangle).
"""
struct Box
  node::TikZ.Node
  inputs::Vector{Port}
  outputs::Vector{Port}
end

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
function to_tikz(f::HomExpr;
    font_size::Number=12, line_width::String="0.4pt", math_mode::Bool=true,
    arrowtip::String="", labels::Bool=false,
    box_size::Number=2, box_style::Dict=Dict(),
    sequence_sep::Number=2, parallel_sep::Number=0.5)::TikZ.Picture
  # Parse arguments.
  # XXX: Storing the style parameters as a global variable is bad practice, but
  # passing them around is really inconvenient. Is there a better approach?
  global style = Dict(
    :math_mode => math_mode, :arrowtip => !isempty(arrowtip), :labels => labels,
    :box_size => box_size, :box_style => box_style,
    :sequence_sep => sequence_sep, :parallel_sep => parallel_sep,
  )
  
  # Draw input and output arrows by composing identities on either side of f. 
  f_seq = collect(HomExpr, head(f) == :compose ? args(f) : [f])
  if head(f) == :id
    insert!(f_seq, 1, id(dom(f)))
  else
    if head(dom(f)) != :munit
      insert!(f_seq, 1, id(dom(f)))
    end
    if head(codom(f)) != :munit
      push!(f_seq, id(codom(f)))
    end
  end
  
  # Create node for extended morphism.
  box_tikz = length(f_seq) == 1 ? box("n", first(f_seq)) : sequence("n", f_seq)
  
  # Create picture with this single node.
  props = [
    TikZ.Property("remember picture"),
    TikZ.Property("font", 
                  "{\\fontsize{$font_size}{$(round(1.2*font_size;digits=2))}}"),
    TikZ.Property("container/.style", "{inner sep=0}"),
    TikZ.Property("every path/.style", "{solid, line width=$line_width}"),
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
function wires(A::ObExpr)::Wires
  error("TikZ wires not implement for $(typeof(A))")
end

""" Create box for a morphism expression.
"""
function box(name::String, f::HomExpr)::Box
  error("TikZ box not implement for $(typeof(f))")
end

# Elements of wiring diagrams
#############################

""" A rectangle, the default style for generators.
"""
function rect(name::String, content::String, dom::Wires, codom::Wires;
              padding::String="0.333em", rounded::Bool=true)::Box
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
  Box(node, dom_ports, codom_ports)
end
function rect(name::String, f::HomExpr{:generator}; kw...)::Box
  rect(name, label(f), wires(dom(f)), wires(codom(f)); kw...)
end

""" A trapezium node, the default style for generators in dagger categories.

The node content is a nested TikZ picture that contains a single visible node.
Nesting pictures even at this level may seem crazy, but it's the only way I know
to get a bounding box on the inner node, regardless of its shape, *before* it's
rendered.
"""
function trapezium(name::String, content::String, dom::Wires, codom::Wires;
                   padding::String="0.333em", rounded::Bool=true,
                   angle::Int=80, reverse::Bool=false)::Box
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
  Box(node, dom_ports, codom_ports)
end
function trapezium(name::String, f::HomExpr{:generator}; kw...)::Box
  trapezium(name, label(f), wires(dom(f)), wires(codom(f)); kw...)
end

""" A triangle node.

Supports any number of inputs and outputs, but looks best with at most one
input and at most one output.
"""
function triangle(name::String, content::String, dom::Wires, codom::Wires;
                  padding::String="0.333em", rounded::Bool=false,
                  reverse::Bool=false)::Box
  dom_ports = [ Port(w, "$name.west", angle=180) for w in dom ]
  codom_ports = [ Port(w, "$name.east", angle=0) for w in codom ]
  box_style = style[:box_style]
  props = [
    TikZ.Property("draw"),
    TikZ.Property("solid"),
    TikZ.Property("inner sep", get(box_style, :padding, padding)),
    TikZ.Property("isosceles triangle"),
    TikZ.Property("isosceles triangle stretches"),
    TikZ.Property("shape border rotate", reverse ? "180" : "0"),
    TikZ.Property(get(box_style, :rounded, rounded) ?
                  "rounded corners" : "sharp corners"),
    TikZ.Property("minimum height", "$(box_size(1))em"),
  ]
  node = TikZ.Node(name; content=content, props=props)
  Box(node, dom_ports, codom_ports)
end
function triangle(name::String, f::HomExpr{:generator}; kw...)::Box
  triangle(name, label(f), wires(dom(f)), wires(codom(f)); kw...)
end

""" Straight lines, used to draw identity morphisms.
"""
function lines(name::String, wires::Wires)::Box
  dom_ports = box_ports(wires, name, dir="center", angle=180)
  codom_ports = box_ports(wires, name, dir="center", angle=0)
  height = box_size(length(wires))
  props = [ TikZ.Property("minimum height", "$(height)em") ]
  node = TikZ.Node(name; props=props)
  Box(node, dom_ports, codom_ports)
end
lines(name::String, A::ObExpr) = lines(name, wires(A))

""" Boxes in sequence, used to draw compositions.
"""
function sequence(name::String, homs::Vector)::Box
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
      
      # Create edge node for label. We use the source port, not the target port
      # (see also `GraphvizWiring`).
      wire = src_port.wire
      node = if (style[:labels] && src_port.show_label && tgt_port.show_label)
        TikZ.EdgeNode(content=wire.label, props=edge_node_props)
      else
        nothing
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
  Box(node, first(mors).inputs, last(mors).outputs)
end

""" Boxes in parallel, used to draw monoidal products.
"""
function parallel(name::String, homs::Vector)::Box
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
  Box(node, inputs, outputs)
end

""" Cross two wires.

Used to draw braid morphisms in symmatric monoidal categories.
""" 
function crossing(name::String, wire1::Wire, wire2::Wire)
  dom = [ Port(wire1, "$name.center", angle=135),
          Port(wire2, "$name.center", angle=225) ]
  codom = [ Port(wire2, "$name.center", angle=45),
            Port(wire1, "$name.center", angle=315) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  Box(node, dom, codom)
end
crossing(name::String, A::ObExpr) = crossing(name, wires(A)...)

""" A junction of wires drawn as a circle.

Used to morphisms in internal monoids and comonoids.

Implemented using a small, visible node for the point and a big, invisible node
as a spacer. FIXME: Is there a more elegant way to achieve the desired margin?
"""
function junction_circle(name::String, wires_in::Wires, wires_out::Wires;
                         fill::Bool=true)
  dom = circle_ports(wires_in, "$name point", "west";
                     show_label = length(wires_in) <= 1)
  codom = circle_ports(wires_out, "$name point", "east";
                       show_label = length(wires_out) <= 1)
  size = box_size(max(length(dom), length(codom)))
  pic = TikZ.Picture(
    TikZ.Node("$name box"; props=[
      TikZ.Property("minimum height", "$(size)em"),
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
  Box(node, dom, codom)
end
function junction_circle(name::String, dom::ObExpr, codom::ObExpr; kw...)
  junction_circle(name, wires(dom), wires(codom); kw...)
end
function junction_circle(name::String, f::HomExpr; kw...)
  junction_circle(name, dom(f), codom(f); kw...)
end

""" A cup.

Used to draw counit morphisms in compact closed categories.
"""
function cup(name::String, wire1::Wire, wire2::Wire)
  ports = [ Port(wire1, "$name.center", angle=90, show_label=false),
            Port(wire2, "$name.center", angle=270, show_label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  Box(node, ports, [])
end
cup(name::String, A::ObExpr) = cup(name, wires(A)...)

""" A cap.

Used to draw unit morphisms in compact closed categories.
"""
function cap(name::String, wire1::Wire, wire2::Wire)
  ports = [ Port(wire1, "$name.center", angle=90, show_label=false),
            Port(wire2, "$name.center", angle=270, show_label=false) ]
  props = [
    TikZ.Property("minimum height", "$(box_size(2))em")
  ]
  node = TikZ.Node(name; props=props)
  Box(node, [], ports)
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
function box_ports(wires::Wires, name::String;
                   dir::String="center", kw...)::Vector{Port}
  box_size, parallel_sep = style[:box_size], style[:parallel_sep]
  m = length(wires)
  if m == 0
    return []
  elseif m == 1
    return [ Port(wires[1], "$name.$dir"; kw...) ]
  end
  
  result = []
  start = (m*box_size + (m-1)*parallel_sep) / 2
  for (i,wire) in enumerate(wires)
    offset = box_size/2 + (i-1)*(box_size+parallel_sep)
    anchor = "\$($name.$dir)+(0,$(start-offset)em)\$"
    push!(result, Port(wire, anchor; kw...))
  end
  return result
end

""" Create ports for a circular node.
"""
function circle_ports(wires::Wires, name::String, dir::String;
                      kw...)::Vector{Port}
  @assert dir in ("west", "east")
  m = length(wires)
  angles = round.(Int, range(0,stop=180,length=m+2)[2:end-1])
  if dir == "west"
    angles = mod.(angles .+ 90, 360)
  elseif dir == "east"
    angles = reverse(mod.(angles .- 90, 360))
  end
  Port[ Port(wire, "$name.$angle"; angle=angle, kw...)
            for (wire, angle) in zip(wires, angles) ]
end

# Defaults
##########

# These methods are reasonable to define for the base expression types since
# they will rarely be changed.

wires(A::ObExpr{:generator}) = [ Wire(label(A)) ]
wires(A::ObExpr{:munit}) = Wire[]
wires(A::ObExpr{:otimes}) = vcat(map(wires, args(A))...)

box(name::String, f::HomExpr{:id}) = lines(name, dom(f))
box(name::String, f::HomExpr{:compose}) = sequence(name, args(f))
box(name::String, f::HomExpr{:otimes}) = parallel(name, args(f))
box(name::String, f::HomExpr{:braid}) = crossing(name, dom(f))

function label(expr::GATExpr{:generator})::String
  sprint(style[:math_mode] ? show_latex : show, expr)
end

""" Default renderers for specific syntax systems.
"""
module Defaults
  import ..TikZWiringDiagrams: Wire, box, wires, label, rect, trapezium,
    junction_circle, cup, cap
  using Catlab.Doctrines
  using Catlab.Syntax
  
  generator(expr::GATExpr)::GATExpr{:generator} = first(expr)
  
  # Category
  box(name::String, f::FreeCategory.Hom{:generator}) = rect(name, f)
  
  # Dagger category
  # Assumes that daggers are fully distributed (as in this syntax system).
  Syntax = FreeDaggerCategory
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    label(generator(f)), wires(dom(f)), wires(codom(f)); reverse=true)

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
  wires(A::Syntax.Ob{:dual}) = [ Wire(label(generator(A)); reverse=true) ]
  box(name::String, f::Syntax.Hom{:generator}) = rect(name, f)
  box(name::String, f::Syntax.Hom{:dunit}) = cap(name, codom(f))
  box(name::String, f::Syntax.Hom{:dcounit}) = cup(name, dom(f))
  
  # Bicategory of relations
  Syntax = FreeBicategoryRelations
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    label(generator(f)), wires(dom(f)), wires(codom(f)); reverse=true)
  box(name::String, f::Syntax.Hom{:dunit}) = cap(name, codom(f))
  box(name::String, f::Syntax.Hom{:dcounit}) = cup(name, dom(f))
  box(name::String, f::Syntax.Hom{:mcopy}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:delete}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:mmerge}) = junction_circle(name, f; fill=false)
  box(name::String, f::Syntax.Hom{:create}) = junction_circle(name, f; fill=false)
  
  Syntax = FreeAbelianBicategoryRelations
  box(name::String, f::Syntax.Hom{:generator}) = trapezium(name, f)
  box(name::String, f::Syntax.Hom{:dagger}) = trapezium(name,
    label(generator(f)), wires(dom(f)), wires(codom(f)); reverse=true)
  box(name::String, f::Syntax.Hom{:dunit}) = cap(name, codom(f))
  box(name::String, f::Syntax.Hom{:dcounit}) = cup(name, dom(f))
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

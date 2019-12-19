""" Backend-agnostic layout of wiring diagrams via morphism expressions.

This module lays out wiring diagrams for visualization, independent of any
specific graphics system. It uses the structure of a morphism expression to
determine the layout. Thus, the first step of the algorithm is to convert the
wiring diagram to a symbolic expression, using the submodule
`WiringDiagrams.Expressions`. Morphism expressions may also be given directly.
"""
module WiringDiagramLayouts
export LayoutOrientation, LeftToRight, RightToLeft, TopToBottom, BottomToTop,
  BoxLayout, PortLayout, layout_diagram

import Base: angle, sign
using Parameters
using StaticArrays: StaticVector, SVector

using ...Syntax
using ...Doctrines: ObExpr, HomExpr, dom, codom, compose, id, otimes, braid
using ...WiringDiagrams

# Data types
############

const AbstractVector2D = StaticVector{2,<:Real}
const Vector2D = SVector{2,Float64}

angle(v::AbstractVector2D) = angle(v[1] + v[2]*im)

""" Orientation of wiring diagram.
"""
@enum LayoutOrientation LeftToRight RightToLeft TopToBottom BottomToTop

is_horizontal(orient::LayoutOrientation) = orient in (LeftToRight, RightToLeft)
is_vertical(orient::LayoutOrientation) = orient in (TopToBottom, BottomToTop)
is_positive(orient::LayoutOrientation) = orient in (LeftToRight, TopToBottom)
is_negative(orient::LayoutOrientation) = orient in (RightToLeft, BottomToTop)
sign(orient::LayoutOrientation) = is_positive(orient) ? +1 : -1

svector(orient::LayoutOrientation) = svector(orient, sign(orient), 0)
svector(orient::LayoutOrientation, first, second) =
  is_horizontal(orient) ? SVector(first, second) : SVector(second, first)

""" Internal data type for configurable options of wiring diagram layout.
"""
@with_kw struct LayoutOptions
  orientation::LayoutOrientation = LeftToRight
  junctions::Bool = true
  base_box_size::Float64 = 2
  sequence_pad::Float64 = 2
  parallel_pad::Float64 = 1
end

""" Layout for box in a wiring diagram.
"""
@with_kw mutable struct BoxLayout{Value}
  value::Value = nothing
  position::Vector2D = zeros(Vector2D)
  size::Vector2D = zeros(Vector2D)
end

lower_corner(layout::BoxLayout) = layout.position - layout.size/2
upper_corner(layout::BoxLayout) = layout.position + layout.size/2
lower_corner(box::AbstractBox) = lower_corner(box.value)
upper_corner(box::AbstractBox) = upper_corner(box.value)

contents_lower_corner(diagram::WiringDiagram) =
  mapreduce(lower_corner, (c,d) -> min.(c,d), boxes(diagram))
contents_upper_corner(diagram::WiringDiagram) =
  mapreduce(upper_corner, (c,d) -> max.(c,d), boxes(diagram))

""" Layout for port in a wiring diagram.
"""
struct PortLayout{Value}
  value::Value
  position::Vector2D     # Position of port relative to box center.
  normal::Vector2D       # Unit normal vector out of port.
end

# Main entry point
##################

""" Lay out a wiring diagram or morphism expression for visualization.

If a wiring diagram is given, it is first to converted to a morphism expression.

The layout is calculated with respect to a cartesian coordinate system with
origin in the top-left corner. Box positions are relative to their centers. All
positions and sizes are dimensionless (unitless).
"""
function layout_diagram(Syntax::Module, diagram::WiringDiagram; kw...)
  layout_wiring_diagram(to_hom_expr(Syntax, diagram); kw...)
end
function layout_diagram(Ob::Type, Hom::Type, diagram::WiringDiagram; kw...)
  layout_wiring_diagram(to_hom_expr(Ob, Hom, diagram); kw...)
end

function layout_diagram(expr::HomExpr; kw...)::WiringDiagram
  opts = LayoutOptions(; kw...)
  diagram = layout_hom_expr(expr, opts)
  layout_ports!(diagram, orientation=opts.orientation)
end

# Layout of boxes
#################

""" Lay out a morphism expression as a wiring diagram.
"""
function layout_hom_expr(expr::HomExpr, opts::LayoutOptions)
  # Default method: singleton diagram.
  inputs, outputs = collect(dom(expr)), collect(codom(expr))
  size = default_box_size(length(inputs), length(outputs), opts)
  box = Box(
    BoxLayout(value=expr, size=size),
    layout_ports(inputs, size, kind=InputPort, orientation=opts.orientation),
    layout_ports(outputs, size, kind=OutputPort, orientation=opts.orientation))
  size_to_fit!(singleton_diagram(box), opts)
end

function layout_hom_expr(expr::HomExpr{:compose}, opts::LayoutOptions)
  subdiagrams = [ layout_hom_expr(arg, opts) for arg in args(expr) ]
  foldl((d1,d2) -> compose_with_layout!(d1, d2, opts), subdiagrams)
end

function layout_hom_expr(expr::HomExpr{:otimes}, opts::LayoutOptions)
  subdiagrams = [ layout_hom_expr(arg, opts) for arg in args(expr) ]
  foldl((d1,d2) -> otimes_with_layout!(d1, d2, opts), subdiagrams)
end

function compose_with_layout!(d1::WiringDiagram, d2::WiringDiagram, opts::LayoutOptions)
  # Compare with `WiringDiagram.compose`.
  diagram = compose(d1, d2; unsubstituted=true)
  dir = svector(opts.orientation)
  place_adjacent!(d1, d2; dir=dir)
  substitute_with_layout!(size_to_fit!(diagram, opts))
end

function otimes_with_layout!(d1::WiringDiagram, d2::WiringDiagram, opts::LayoutOptions)
  # Compare with `WiringDiagrams.otimes`.
  diagram = otimes(d1, d2; unsubstituted=true)
  dir = svector(opts.orientation, 0, 1)
  place_adjacent!(d1, d2; dir=dir)
  substitute_with_layout!(size_to_fit!(diagram, opts))
end

""" Size a wiring diagram to fit its contents.

The inner boxes are also shifted to be centered within the new bounds.
"""
function size_to_fit!(diagram::WiringDiagram, opts::LayoutOptions)
  nin, nout = length(input_ports(diagram)), length(output_ports(diagram))
  minimum_size = default_box_size(nin, nout, opts)
  
  lower, upper = contents_lower_corner(diagram), contents_upper_corner(diagram)
  content_size = upper - lower
  pad = svector(opts.orientation, opts.sequence_pad, opts.parallel_pad)
  size = max.(minimum_size, content_size + pad)
  
  shift_boxes!(diagram, (size-content_size)/2 - lower)
  diagram.value = BoxLayout(size=size)
  diagram
end

""" Substitute sub-wiring diagrams, preserving their layouts.
"""
function substitute_with_layout!(d::WiringDiagram)
  substitute_with_layout!(d, filter(v -> box(d,v) isa WiringDiagram, box_ids(d)))
end
function substitute_with_layout!(d::WiringDiagram, vs::Vector{Int})
  for v in vs
    sub = box(d, v)::WiringDiagram
    shift_boxes!(sub, lower_corner(sub))
  end
  substitute(d, vs)
end

""" Place one box adjacent to another.

The absolute positions are undefined; only relative positions are guaranteed.
"""
function place_adjacent!(box1::AbstractBox, box2::AbstractBox;
                         dir::AbstractVector2D=SVector(1,0))
  layout1, layout2 = box1.value::BoxLayout, box2.value::BoxLayout
  layout1.position = -layout1.size/2 .* dir
  layout2.position = layout2.size/2 .* dir
end

""" Shift all boxes within wiring diagram by a fixed offset.
"""
function shift_boxes!(diagram::WiringDiagram, offset::AbstractVector2D)
  for box in boxes(diagram)
    layout = box.value::BoxLayout
    layout.position += offset
  end
  diagram
end

""" Compute the default size of a box based on the number of its ports.

We use the unique formula consistent with the padding for monoidal products,
ensuring that the size of a product of boxes depends only on the total number of
ports, not on the number of boxes.
"""
function default_box_size(nin::Int, nout::Int, opts::LayoutOptions)
  base_size = opts.base_box_size
  n = max(1, nin, nout)
  svector(opts.orientation, base_size, n*base_size + (n-1)*opts.parallel_pad)
end

# Layout of ports
#################

""" Lay out ports for a rectangular box.

The ports are evenly spaced within the available area.
"""
function layout_ports(port_values::Vector, box_size::Vector2D;
    kind::PortKind=input, orientation::LayoutOrientation=LeftToRight)::Vector{PortLayout}
  normal_dir = (kind == InputPort ? -1.0 : +1.0) * svector(orientation)
  start = box_size/2 .* normal_dir
  
  offset = box_size/2 .* svector(orientation, 0, 1)
  n = length(port_values)
  coeffs = range(-1, 1, length=n+2)[2:n+1]
  PortLayout[ PortLayout(value, start + coeff .* offset, normal_dir)
              for (value, coeff) in zip(port_values, coeffs) ]
end

function layout_ports!(diagram::WiringDiagram; kw...)
  layout = diagram.value::BoxLayout
  diagram.input_ports = layout_ports(
    input_ports(diagram), layout.size; kind=InputPort, kw...)
  diagram.output_ports = layout_ports(
    output_ports(diagram), layout.size; kind=OutputPort, kw...)
  diagram
end

end

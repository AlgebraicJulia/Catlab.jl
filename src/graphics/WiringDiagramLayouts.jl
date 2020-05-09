""" Backend-agnostic layout of wiring diagrams via morphism expressions.

This module lays out wiring diagrams for visualization, independent of any
specific graphics system. It uses the structure of a morphism expression to
determine the layout. Thus, the first step of the algorithm is to convert the
wiring diagram to a symbolic expression, using the submodule
`WiringDiagrams.Expressions`. Morphism expressions may also be given directly.
"""
module WiringDiagramLayouts
export LayoutOrientation, LeftToRight, RightToLeft, TopToBottom, BottomToTop,
  layout_diagram, layout_box

using Compat
import Base: sign
using LinearAlgebra: dot, normalize
using Logging
using Parameters
using StaticArrays: StaticVector, SVector
using Statistics: mean

using ...Syntax
using ...Doctrines: ObExpr, HomExpr, dom, codom, compose, id, otimes, braid
using ...WiringDiagrams

# Data types
############

const AbstractVector2D = StaticVector{2,<:Real}
const Vector2D = SVector{2,Float64}

""" Orientation of wiring diagram.
"""
@enum LayoutOrientation LeftToRight RightToLeft TopToBottom BottomToTop

is_horizontal(orient::LayoutOrientation) = orient in (LeftToRight, RightToLeft)
is_vertical(orient::LayoutOrientation) = orient in (TopToBottom, BottomToTop)
is_positive(orient::LayoutOrientation) = orient in (LeftToRight, TopToBottom)
is_negative(orient::LayoutOrientation) = orient in (RightToLeft, BottomToTop)

sign(orient::LayoutOrientation) = is_positive(orient) ? +1 : -1
port_sign(kind::PortKind, orient::LayoutOrientation) =
  (kind == InputPort ? -1 : +1) * sign(orient)
port_sign(d::WiringDiagram, port::Port, orient::LayoutOrientation) =
  (port.box in outer_ids(d) ? -1 : +1) * port_sign(port.kind, orient)

svector(orient::LayoutOrientation, first, second) =
  is_horizontal(orient) ? SVector(first, second) : SVector(second, first)

""" Internal data type for configurable options of wiring diagram layout.
"""
@with_kw_noshow struct LayoutOptions
  orientation::LayoutOrientation = LeftToRight
  default_box_shape::Symbol = :rectangle
  box_shapes::AbstractDict = Dict()
  box_styles::AbstractDict = Dict()
  outer_ports_layout::Symbol = :isotonic
  anchor_wires::Union{Bool,AbstractSet,AbstractVector} = [:id,:braid]
  base_box_size::Real = 2
  box_stretch::Real = 1
  sequence_pad::Real = 2
  parallel_pad::Real = 1
  junction_size::Real = 0.25
end

svector(opts::LayoutOptions, args...) = svector(opts.orientation, args...)

""" Layout for box in a wiring diagram.

Suggests a shape, size, and position for the box. Also includes the box's
value, typically used for labels, and a style name, which does not affect the
layout but is interpreted by graphics backends to adjust the visual style.

Specific features of the shape are determined by the graphics backend. For
example, a rectangle could be rendered with or without rounded corners or even
as another, similar shape, such as a parallelogram.
"""
@with_kw_noshow mutable struct BoxLayout{Value}
  value::Value = nothing
  shape::Symbol = :rectangle
  position::Vector2D = zeros(Vector2D)
  size::Vector2D = zeros(Vector2D)
  style::Union{Symbol,Nothing} = nothing
end

position(layout::BoxLayout) = layout.position
size(layout::BoxLayout) = layout.size
lower_corner(layout::BoxLayout) = position(layout) - size(layout)/2
upper_corner(layout::BoxLayout) = position(layout) + size(layout)/2

position(box::AbstractBox) = position(box.value)
size(box::AbstractBox) = size(box.value)
lower_corner(box::AbstractBox) = lower_corner(box.value)
upper_corner(box::AbstractBox) = upper_corner(box.value)

contents_lower_corner(diagram::WiringDiagram) =
  mapreduce(lower_corner, (c,d) -> min.(c,d), boxes(diagram))
contents_upper_corner(diagram::WiringDiagram) =
  mapreduce(upper_corner, (c,d) -> max.(c,d), boxes(diagram))

""" Layout for port in a wiring diagram.
"""
@with_kw_noshow struct PortLayout{Value}
  value::Value = nothing
  position::Vector2D = zeros(Vector2D) # Position relative to box center.
  normal::Vector2D = zeros(Vector2D)   # Outward unit normal vector.
  label_wires::Bool = true             # Show labels for wires into/out of port?
  reverse_wires::Bool = false          # Reverse wires into/out of port?
end

position(layout::PortLayout) = layout.position
normal(layout::PortLayout) = layout.normal

""" Interior point of wire in a wiring diagram.
"""
mutable struct WirePoint
  position::Vector2D     # Position of wire at point.
  tangent::Vector2D      # Unit tangent vector along wire at point.
end

position(point::WirePoint) = point.position
tangent(point::WirePoint) = point.tangent

const WireLayout = Union{Vector{WirePoint},Nothing}

wire_points(points::Vector{WirePoint}) = points
wire_points(::Nothing) = WirePoint[]
wire_points(wire::Wire) = wire_points(wire.value)

# Main entry point
##################

""" Lay out a wiring diagram or morphism expression for visualization.

If a wiring diagram is given, it is first to converted to a morphism expression.

The layout is calculated with respect to a cartesian coordinate system with
origin at the center of the diagram and the positive y-axis pointing
*downwards*. Box positions are relative to their centers. All positions and
sizes are dimensionless (unitless).
"""
function layout_diagram(Syntax::Module, diagram::WiringDiagram; kw...)
  layout_diagram(to_hom_expr(Syntax, diagram); kw...)
end
function layout_diagram(Ob::Type, Hom::Type, diagram::WiringDiagram; kw...)
  layout_diagram(to_hom_expr(Ob, Hom, diagram); kw...)
end

function layout_diagram(expr::HomExpr; kw...)::WiringDiagram
  opts = LayoutOptions(; kw...)
  diagram = layout_hom_expr(expr, opts)
  layout_outer_ports!(diagram, opts, method=opts.outer_ports_layout)
end

# Morphism expression layout
############################

""" Lay out a morphism expression as a wiring diagram.
"""
layout_hom_expr(f::HomExpr, opts) = layout_box(f, opts)

layout_hom_expr(f::HomExpr{:compose}, opts) =
  compose_with_layout!(map(arg -> layout_hom_expr(arg, opts), args(f)), opts)
layout_hom_expr(f::HomExpr{:otimes}, opts) =
  otimes_with_layout!(map(arg -> layout_hom_expr(arg, opts), args(f)), opts)

layout_hom_expr(f::HomExpr{:id}, opts) = layout_pure_wiring(f, opts)
layout_hom_expr(f::HomExpr{:braid}, opts) = layout_pure_wiring(f, opts)

layout_hom_expr(f::HomExpr{:mcopy}, opts) = layout_supply(f, opts, shape=:junction)
layout_hom_expr(f::HomExpr{:delete}, opts) = layout_supply(f, opts, shape=:junction)
layout_hom_expr(f::HomExpr{:mmerge}, opts) = layout_supply(f, opts, shape=:junction)
layout_hom_expr(f::HomExpr{:create}, opts) = layout_supply(f, opts, shape=:junction)

layout_hom_expr(f::HomExpr{:plus}, opts) =
  layout_supply(f, opts, shape=:junction, style=:variant_junction)
layout_hom_expr(f::HomExpr{:zero}, opts) =
  layout_supply(f, opts, shape=:junction, style=:variant_junction)
layout_hom_expr(f::HomExpr{:coplus}, opts) =
  layout_supply(f, opts, shape=:junction, style=:variant_junction)
layout_hom_expr(f::HomExpr{:cozero}, opts) =
  layout_supply(f, opts, shape=:junction, style=:variant_junction)

layout_hom_expr(f::HomExpr{:dunit}, opts) =
  layout_supply(f, opts, shape=:junction, visible=false, pad=false)
layout_hom_expr(f::HomExpr{:dcounit}, opts) =
  layout_supply(f, opts, shape=:junction, visible=false, pad=false)
  
layout_port(A::ObExpr{:dual}; kw...) =
  PortLayout(; value=A, reverse_wires=true, kw...)
wire_label(mime::MIME, A::ObExpr{:dual}) = wire_label(mime, first(A))

function layout_box(f::HomExpr, opts::LayoutOptions; kw...)
  layout_box(collect(dom(f)), collect(codom(f)), opts; value=f, kw...)
end

function layout_pure_wiring(f::HomExpr, opts::LayoutOptions; kw...)
  layout_pure_wiring(to_wiring_diagram(f, identity, identity), opts;
    anchor_wires=head(f) in opts.anchor_wires, kw...)
end

function layout_supply(f::HomExpr, opts::LayoutOptions;
                       ob::Union{ObExpr,Nothing}=nothing, kw...)
  obs = collect(isnothing(ob) ? first(f)::ObExpr : ob)
  n = length(obs)
  ndom, ncodom = ndims(dom(f)) ÷ n, ndims(codom(f)) ÷ n
  diagram = otimes_with_layout!(map(obs) do ob
    layout_box(repeat([ob], ndom), repeat([ob], ncodom), opts; kw...)
  end, opts)
  anchor_wires = head(f) in opts.anchor_wires
  if n > 1 && ndom > 1
    σ = reshape(permutedims(reshape(1:ndom*n, n, :)), :)
    σ_diagram = permute(dom(diagram), σ, inverse=true)
    σ_diagram = layout_pure_wiring(σ_diagram, opts, anchor_wires=anchor_wires)
    diagram = compose_with_layout!(σ_diagram, diagram, opts)
  end
  if n > 1 && ncodom > 1
    σ = reshape(permutedims(reshape(1:ncodom*n, n, :)), :)
    σ_diagram = permute(codom(diagram), σ)
    σ_diagram = layout_pure_wiring(σ_diagram, opts, anchor_wires=anchor_wires)
    diagram = compose_with_layout!(diagram, σ_diagram, opts)
  end
  diagram
end

# Diagram layout
################

""" Compose wiring diagrams and their layouts.

Compare with: `WiringDiagram.compose`.
"""
function compose_with_layout!(d1::WiringDiagram, d2::WiringDiagram, opts::LayoutOptions)
  diagram = compose(d1, d2; unsubstituted=true)
  dir = svector(opts, sign(opts.orientation), 0)
  place_adjacent!(d1, d2; dir=dir, pad=-opts.sequence_pad)
  substitute_with_layout!(size_to_fit!(diagram, opts, pad=false))
end
function compose_with_layout!(diagrams::Vector{<:WiringDiagram}, opts::LayoutOptions)
  foldl((d1,d2) -> compose_with_layout!(d1, d2, opts), diagrams)
end

""" Tensor wiring diagrams and their layouts.

Compare with: `WiringDiagram.otimes`.
"""
function otimes_with_layout!(d1::WiringDiagram, d2::WiringDiagram, opts::LayoutOptions)
  # Compare with `WiringDiagrams.otimes`.
  diagram = otimes(d1, d2; unsubstituted=true)
  dir = svector(opts, 0, 1)
  place_adjacent!(d1, d2; dir=dir, pad=-opts.parallel_pad)
  substitute_with_layout!(size_to_fit!(diagram, opts, pad=false))
end
function otimes_with_layout!(diagrams::Vector{<:WiringDiagram}, opts::LayoutOptions)
  foldl((d1,d2) -> otimes_with_layout!(d1, d2, opts), diagrams)
end

""" Size a wiring diagram to fit its contents.

The inner boxes are also shifted to be centered within the new bounds.
"""
function size_to_fit!(diagram::WiringDiagram, opts::LayoutOptions; pad::Bool=true)
  nin, nout = length(input_ports(diagram)), length(output_ports(diagram))
  minimum_size = minimum_diagram_size(nin, nout, opts)
  
  lower, upper = contents_lower_corner(diagram), contents_upper_corner(diagram)
  content_size = upper - lower
  if pad; content_size += 2 * diagram_padding(opts) end
  size = max.(minimum_size, content_size)
  
  content_center = (lower + upper)/2
  shift_contents!(diagram, -content_center)
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
    shift_contents!(sub, position(sub))
  end
  substitute(d, vs; merge_wire_values=merge_wire_layouts)
end

""" Place one box adjacent to another.

The absolute positions are undefined; only relative positions are guaranteed.
"""
function place_adjacent!(box1::AbstractBox, box2::AbstractBox;
                         dir::AbstractVector2D=SVector(1,0), pad::Real=0)
  layout1, layout2 = box1.value::BoxLayout, box2.value::BoxLayout
  layout1.position = -(pad .+ size(layout1))/2 .* dir
  layout2.position = (pad .+ size(layout2))/2 .* dir
end

""" Shift all boxes and wires within wiring diagram by a fixed offset.
"""
function shift_contents!(diagram::WiringDiagram, offset::AbstractVector2D)
  for box in boxes(diagram)
    layout = box.value::BoxLayout
    layout.position += offset
  end
  for wire in wires(diagram)
    for point in wire_points(wire)
      point.position += offset
    end
  end
  diagram
end

""" Compute the minimum size of a wiring diagram from the number of its ports.
"""
function minimum_diagram_size(nin::Int, nout::Int, opts::LayoutOptions)
  default_box_size(nin, nout, opts, stretch=0) + 2*diagram_padding(opts)
end
function diagram_padding(opts::LayoutOptions)
  svector(opts, opts.sequence_pad, opts.parallel_pad)
end

# Box layout
############

""" Lay out a box and its ports.

By default the box is rectangular, but other shapes are also supported.
"""
function layout_box(inputs::Vector, outputs::Vector, opts::LayoutOptions;
                    shape::Union{Symbol,Nothing}=nothing,
                    style::Union{Symbol,Nothing}=nothing, value=nothing, kw...)
  shape = get(opts.box_shapes, value) do
    isnothing(shape) ? opts.default_box_shape : shape
  end
  style = get(opts.box_styles, value, style)
  layout_box(Val(shape), inputs, outputs, opts; style=style, value=value, kw...)
end

function layout_box(::Val{:rectangle}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; shape::Symbol=:rectangle, kw...)
  size = default_box_size(length(inputs), length(outputs), opts)
  box = Box(BoxLayout(; shape=shape, size=size, kw...),
            layout_linear_ports(InputPort, inputs, size, opts),
            layout_linear_ports(OutputPort, outputs, size, opts))
  size_to_fit!(singleton_diagram(box), opts)
end

function layout_box(::Val{:circle}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; pad::Bool=true, kw...)
  size = default_box_size(1, 1, opts)
  radius = first(size) / 2
  box = Box(BoxLayout(; shape=:circle, size=size, kw...),
            layout_circular_ports(InputPort, inputs, radius, opts; pad=pad),
            layout_circular_ports(OutputPort, outputs, radius, opts; pad=pad))
  size_to_fit!(singleton_diagram(box), opts)
end

function layout_box(::Val{:ellipse}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; pad::Bool=true, kw...)
  size = default_box_size(length(inputs), length(outputs), opts)
  radii = size / 2
  box = Box(BoxLayout(; shape=:ellipse, size=size, kw...),
            layout_elliptical_ports(InputPort, inputs, radii, opts; pad=pad),
            layout_elliptical_ports(OutputPort, outputs, radii, opts; pad=pad))
  size_to_fit!(singleton_diagram(box), opts)
end

function layout_box(::Val{:triangle}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; kw...)
  @assert length(inputs) <= 1 "Cannot use triangle shape with multiple inputs"
  layout_box(Val(:rectangle), inputs, outputs, opts; shape=:triangle, kw...)
end
function layout_box(::Val{:invtriangle}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; kw...)
  @assert length(outputs) <= 1 "Cannot use invtriangle shape with multiple outputs"
  layout_box(Val(:rectangle), inputs, outputs, opts; shape=:invtriangle, kw...)
end

# Although `trapezoid` is the standard term in North American English,
# we use the term `trapezium` because both Graphviz and TikZ do. 
function layout_box(::Val{:trapezium}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; kw...)
  layout_box(Val(:rectangle), inputs, outputs, opts; shape=:trapezium, kw...)
end
function layout_box(::Val{:invtrapezium}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; kw...)
  layout_box(Val(:rectangle), inputs, outputs, opts; shape=:invtrapezium, kw...)
end

function layout_box(::Val{:junction}, inputs::Vector, outputs::Vector,
                    opts::LayoutOptions; visible::Bool=true, pad::Bool=true, kw...)
  nin, nout = length(inputs), length(outputs)
  shape, radius = visible ? (:junction, opts.junction_size) : (:invisible, 0)
  size = 2*SVector(radius, radius)
  box = Box(BoxLayout(; shape=shape, size=size, kw...),
            layout_circular_ports(InputPort, inputs, radius, opts;
                                  pad=pad, label_wires = nin == 1 || nout == 0),
            layout_circular_ports(OutputPort, outputs, radius, opts;
                                  pad=pad, label_wires = nin == 0 || nout == 1))
  size_to_fit!(singleton_diagram(box), opts)
end

""" Compute the default size of a rectangular box from the number of its ports.

We use the unique formula consistent with the padding for monoidal products,
ensuring that the size of a product of boxes depends only on the total number of
ports, not on the number of boxes.
"""
function default_box_size(nin::Int, nout::Int, opts::LayoutOptions;
                          stretch::Union{Real,Nothing}=nothing)
  base_size = opts.base_box_size
  stretch = isnothing(stretch) ? opts.box_stretch : stretch
  n = max(1, nin, nout)
  svector(opts, stretch*base_size, n*base_size + (n-1)*opts.parallel_pad)
end

# Port layout
#############

""" Lay out ports linearly, for use with a rectangular box.

Assumes the box is at least as large as `default_box_size()`.
"""
function layout_linear_ports(port_kind::PortKind, port_values::Vector,
                             box_size::AbstractVector2D, opts::LayoutOptions; kw...)
  n = length(port_values)
  coeffs = range(-(n-1), n-1, step=2) / 2 # Always length n
  coords = (opts.base_box_size + opts.parallel_pad) .* collect(coeffs)
  layout_linear_ports(port_kind, port_values, coords, box_size, opts, kw...)
end

function layout_linear_ports(port_kind::PortKind, port_values::Vector, 
                             port_coords::Vector, box_size::AbstractVector2D,
                             opts::LayoutOptions; kw...)
  normal_dir = svector(opts, port_sign(port_kind, opts.orientation), 0.0)
  port_dir = svector(opts, 0.0, 1.0)
  start = box_size/2 .* normal_dir
  positions = [ start + coord .* port_dir for coord in port_coords ]
  PortLayout[ layout_port(value, position=pos, normal=normal_dir; kw...)
              for (value, pos) in zip(port_values, positions) ]
end

""" Lay out ports along a circular arc.
"""
function layout_circular_ports(port_kind::PortKind, port_values::Vector,
                               radius::Real, opts::LayoutOptions; kw...)
  radii = SVector(radius, radius)
  layout_elliptical_ports(port_kind, port_values, radii, opts; kw...)
end

""" Lay out ports along an elliptical arc.
"""
function layout_elliptical_ports(port_kind::PortKind, port_values::Vector,
                                 radii::AbstractVector2D, opts::LayoutOptions;
                                 pad::Bool=true, kw...)
  n = length(port_values)
  port_dir = svector(opts, port_sign(port_kind, opts.orientation), 0)
  θ1, θ2 = if port_dir == SVector(1,0); (π/2, -π/2)
    elseif port_dir == SVector(0,1); (-π, 0)
    elseif port_dir == SVector(-1,0); (π/2, 3π/2)
    elseif port_dir == SVector(0,-1); (π, 0) end
  θs = collect(pad ? range(θ1,θ2,length=n+2)[2:n+1] : range(θ1,θ2,length=n))
  dirs = [ SVector(cos(θ),-sin(θ)) for θ in θs ] # positive y-axis downwards
  PortLayout[ layout_port(value, position=radii .* dir, normal=dir; kw...)
              for (value, dir) in zip(port_values, dirs) ]
end

""" Lay out outer ports of wiring diagram.
"""
function layout_outer_ports!(diagram::WiringDiagram, opts::LayoutOptions; kw...)
  original_value = x -> x isa PortLayout ? x.value : x # XXX: This is ugly.
  diagram.input_ports = map(original_value, input_ports(diagram))
  diagram.output_ports = map(original_value, output_ports(diagram))
  diagram.input_ports, diagram.output_ports =
    layout_outer_ports(diagram, opts; kw...)
  diagram
end

""" Lay out outer ports of wiring diagram.
"""
function layout_outer_ports(diagram::WiringDiagram, opts::LayoutOptions;
                            method::Symbol=:fixed, kw...)
  if !has_port_layout_method(method)
    if method == :isotonic
      @warn """
        Both Convex.jl and SCS.jl must be loaded to use isotonic
        regression for port layout. Falling back to fixed layout.
        """ maxlog=1
    else
      error("Unknown port layout method: $method")
    end
    method = :fixed
  end
  layout_outer_ports(diagram, opts, Val(method); kw...)
end

function layout_outer_ports(diagram::WiringDiagram, opts::LayoutOptions,
                            ::Val{:fixed})
  (layout_linear_ports(InputPort, input_ports(diagram), size(diagram), opts),
   layout_linear_ports(OutputPort, output_ports(diagram), size(diagram), opts))
end

function layout_outer_ports(diagram::WiringDiagram, opts::LayoutOptions,
                            ::Val{:isotonic})
  inputs, outputs = input_ports(diagram), output_ports(diagram)
  diagram_size = diagram.value.size
  port_dir = svector(opts, 0, 1)
  port_coord = v -> dot(v, port_dir)
  max_range = port_coord(diagram_size)
  lower, upper = -max_range/2, max_range/2
  pad = opts.base_box_size + opts.parallel_pad
  
  # Solve optimization problem for input ports.
  # Note that we are minimizing distance only along the port axis, not in the
  # full Euclidean plan.
  ys = [ Float64[] for i in eachindex(inputs) ]
  for wire in out_wires(diagram, input_id(diagram))
    i, layout = wire.source.port, wire.value::WireLayout
    if !(isnothing(layout) || isempty(layout))
      push!(ys[i], port_coord(position(first(layout))))
    elseif wire.target.box != output_id(diagram)
      push!(ys[i], port_coord(position(diagram, wire.target)))
    end
  end
  y = Float64[ isempty(y) ? 0.0 : mean(y) for y in ys ]
  in_coords = solve_isotonic(y; lower=lower, upper=upper, pad=pad)
  
  # Solve optimization problem for output ports.
  ys = [ Float64[] for i in eachindex(outputs) ]
  for wire in in_wires(diagram, output_id(diagram))
    i, layout = wire.target.port, wire.value::WireLayout
    if !(isnothing(layout) || isempty(layout))
      push!(ys[i], port_coord(position(last(layout))))
    elseif wire.source.box != input_id(diagram)
      push!(ys[i], port_coord(position(diagram, wire.source)))
    end
  end
  y = Float64[ isempty(y) ? 0.0 : mean(y) for y in ys ]
  out_coords = solve_isotonic(y; lower=lower, upper=upper, pad=pad)
  
  (layout_linear_ports(InputPort, inputs, in_coords, diagram_size, opts),
   layout_linear_ports(OutputPort, outputs, out_coords, diagram_size, opts))
end
solve_isotonic(args...; kw...) = error("Isotonic regression backend not available")

has_port_layout_method(method::Symbol) = has_port_layout_method(Val(method))
has_port_layout_method(::Val) = false
has_port_layout_method(::Val{:fixed}) = true

layout_port(value; kw...) = PortLayout(; value=value, kw...)

function position(diagram::WiringDiagram, port::Port)
  pos = position(port_value(diagram, port))
  if !(port.box in outer_ids(diagram))
    pos += position(box(diagram, port.box))
  end
  pos
end

function normal(diagram::WiringDiagram, port::Port)
  (port.box in outer_ids(diagram) ? -1 : +1) * normal(port_value(diagram, port))
end

# Wire layout
#############

""" Lay out the wires in a wiring diagram with no boxes.
"""
function layout_pure_wiring(diagram::WiringDiagram, opts::LayoutOptions;
                            anchor_wires::Bool=true)
  @assert nboxes(diagram) == 0
  inputs, outputs = input_ports(diagram), output_ports(diagram)
  size = minimum_diagram_size(length(inputs), length(outputs), opts)
  result = WiringDiagram(BoxLayout(size=size), inputs, outputs)
  if anchor_wires
    result = layout_outer_ports!(result, opts, method=:fixed)
    e1, e2 = svector(opts, 1, 0), svector(opts, 0, 1)
    for wire in wires(diagram)
      src, tgt = wire.source, wire.target
      src_pos, tgt_pos = (position(port_value(result, p)) for p in (src, tgt))
      mid_pos = (src_pos + tgt_pos) / 2
      v = sign.((tgt_pos - src_pos) .* e1) + (tgt.port - src.port) .* e2
      point = WirePoint(mid_pos .* e2, normalize(v))
      add_wire!(result, Wire([point], src, tgt))
    end
  else
    add_wires!(result, wires(diagram))
  end
  result
end

merge_wire_layouts(left::WireLayout, middle::WireLayout, right::WireLayout) =
  vcat(wire_points(left), wire_points(middle), wire_points(right))

# Labels
########

""" Label for box in wiring diagram.
"""
box_label(mime::MIME, value) = diagram_element_label(mime, value)

""" Label for wire in wiring diagram.

Note: This function takes a port value, not a wire value.
"""
wire_label(mime::MIME, value) = diagram_element_label(mime, value)

""" Label for element in wiring diagram.

By default, both `box_label` and `wire_label` fall back to this function.
"""
diagram_element_label(::MIME, value) = string(value)
diagram_element_label(::MIME, ::Nothing) = ""

function diagram_element_label(::MIME"text/latex", expr::GATExpr)
  string('$', sprint(show_latex, expr), '$')
end
function diagram_element_label(::MIME"text/latex", s::Union{String,Symbol})
  string('$', s, '$')
end

end

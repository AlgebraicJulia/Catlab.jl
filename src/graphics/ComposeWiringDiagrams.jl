""" Draw wiring diagrams using Compose.jl.
"""
module ComposeWiringDiagrams
export ComposePicture, to_composejl, layout_to_composejl

using Compat
using LinearAlgebra: dot
using Parameters
import Compose
const C = Compose

using ...WiringDiagrams
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: AbstractVector2D, Vector2D, BoxLayout, box_label,
  position, size, lower_corner, upper_corner, normal, tangent, wire_points

# Data types
############

""" A Compose context together with a given width and height.

We need this type because contexts have no notion of size or aspect ratio, but
wiring diagram layouts have fixed aspect ratios.
"""
struct ComposePicture
  context::Compose.Context
  width::Compose.Measure
  height::Compose.Measure
end

function Base.show(io::IO, ::MIME"text/html", pic::ComposePicture)
  jsmode = C.default_jsmode
  C.draw(C.SVGJS(io, pic.width, pic.height, false, jsmode=jsmode), pic.context)
end
function Base.show(io::IO, ::MIME"image/svg+xml", pic::ComposePicture)
  C.draw(C.SVG(io, pic.width, pic.height, false), pic.context)
end

const ComposeProperties = AbstractVector{<:Compose.Property}

""" Internal data type for configurable options of Compose.jl wiring diagrams.
"""
@with_kw_noshow struct ComposeOptions
  base_unit::Compose.Measure = 4*C.mm
  props::AbstractDict = Dict()
  box_renderer::Function = render_box
  background_color::Union{AbstractString,C.Colorant,Nothing} = nothing
  rounded_boxes::Bool = true
end

# Wiring diagrams
#################

""" Draw a wiring diagram in Compose.jl.
"""
function to_composejl(args...; kw...)::ComposePicture
  layout_kw = filter(p -> first(p) ∉ fieldnames(ComposeOptions), kw)
  diagram = layout_diagram(args...; layout_kw...)
  
  compose_kw = filter(p -> first(p) ∈ fieldnames(ComposeOptions), kw)
  layout_to_composejl(diagram; compose_kw...)
end

""" Draw a wiring diagram in Compose.jl using the given layout.
"""
function layout_to_composejl(diagram::WiringDiagram; props=Dict(), kw...)
  props = merge(default_props, props)
  opts = ComposeOptions(; props=props, kw...)
  context = layout_to_context(diagram, opts)
  if !isnothing(opts.background_color)
    context = C.compose(C.context(),
      context,
      (C.context(), C.rectangle(), C.fill(opts.background_color)))
  end
  ComposePicture(context, (opts.base_unit .* size(diagram))...)
end

function layout_to_context(diagram::WiringDiagram, opts::ComposeOptions)
  # The origin of the Compose.jl coordinate system is in the top-left corner,
  # while the origin of wiring diagram layout is at the diagram center, so we
  # need to translate the coordinates using the `UnitBox`.
  units = C.UnitBox(-size(diagram)/2..., size(diagram)...)
  C.compose(C.context(units=units, tag=:diagram),
    C.compose(C.context(tag=:boxes),
      map(boxes(diagram)) do box
        layout_to_context(box, opts)
      end...
    ),
    C.compose(C.context(tag=:wires),
      map(wires(diagram)) do wire
        layout_to_context(diagram, wire, opts)
      end...
    ),
  )
end

function layout_to_context(box::Box, opts::ComposeOptions)
  C.compose(C.context(lower_corner(box)..., size(box)...,
                      units=C.UnitBox(), tag=:box),
    opts.box_renderer(box.value, opts)
  )
end

function layout_to_context(diagram::WiringDiagram, wire::Wire, opts::ComposeOptions)
  src, tgt = wire.source, wire.target
  src_pos, tgt_pos = position(diagram, src), position(diagram, tgt)
  points = [ src_pos ]
  prev = (src_pos, normal(diagram, src))
  for point in wire_points(wire)
    p, v = position(point), tangent(point)
    append!(points, tangents_to_controls(prev..., -v, p))
    push!(points, p)
    prev = (p, v)
  end
  append!(points, tangents_to_controls(prev..., normal(diagram, tgt), tgt_pos))
  push!(points, tgt_pos)
  
  C.compose(C.context(tag=:wire),
    piecewise_curve(map(Tuple, points)),
    opts.props[:wire]...
  )
end

""" Control points for Bezier curve from endpoints and unit tangent vectors.
"""
function tangents_to_controls(p1::AbstractVector2D, v1::AbstractVector2D,
    v2::AbstractVector2D, p2::AbstractVector2D; weight::Float64=0.5)
  v = p2 - p1
  (p1 + weight * dot(v,v1) * v1, p2 - weight * dot(v,v2) * v2)
end

""" Draw an atomic box in Compose.jl.
"""
function render_box(layout::BoxLayout, opts::ComposeOptions)
  render_box(Val(layout.shape), layout, opts)
end
function render_box(::Val{:rectangle}, layout::BoxLayout, opts::ComposeOptions)
  form = opts.rounded_boxes ? rounded_rectangle() : C.rectangle()
  labeled_box(form, layout, opts)
end
render_box(::Val{:circle}, layout::BoxLayout, opts::ComposeOptions) =
  labeled_box(C.circle(), layout, opts)
render_box(::Val{:ellipse}, layout::BoxLayout, opts::ComposeOptions) =
  labeled_box(C.ellipse(), layout, opts)
render_box(::Val{:junction}, layout::BoxLayout, opts::ComposeOptions) =
  C.compose(C.context(), C.circle(), box_props(layout, opts)...)
render_box(::Val{:invisible}, ::BoxLayout, ::ComposeOptions) = C.context()

function labeled_box(form::C.ComposeNode, layout::BoxLayout, opts::ComposeOptions)
  labeled_form(form, box_label(MIME("text/plain"), layout.value),
    form_props=box_props(layout, opts), text_props=opts.props[:text])
end

""" Get Compose.jl properties for box.
"""
function box_props(layout::BoxLayout, opts::ComposeOptions)
  style = if isnothing(layout.style)
    layout.shape in (:junction, :invisible) ? layout.shape : :box
  else
    layout.style
  end
  opts.props[style]
end

# Compose.jl forms
##################

""" Draw a form with centered text label in Compose.
"""
function labeled_form(form::C.ComposeNode, label::String; rounded::Bool=true,
    form_props::ComposeProperties=[], text_props::ComposeProperties=[])
  C.compose(C.context(),
    (C.context(order=1), form, form_props...),
    (C.context(order=2),
     C.text(0.5, 0.5, label, C.hcenter, C.vcenter),
     text_props...),
  )
end

""" Draw a rounded rectangle in Compose.
"""
function rounded_rectangle(args...; corner_radius::Compose.Measure=C.mm)
  w, h, px = Compose.w, Compose.h, Compose.px
  r = corner_radius
  C.compose(C.context(args...),
    C.compose(C.context(order=1),
      # Layer 1: fill.
      # Since we cannot use a stroke here, we add a single pixel fudge factor to
      # prevent a small but visible gap between the different fill regions.
      C.rectangle(r-1px, 0h, 1w-2r+2px, 1h),
      C.rectangle(0w, r-1px, 1w, 1h-2r+2px),
      C.sector(r,    r,    r, π,    3π/2),
      C.sector(1w-r, r,    r, 3π/2, 0),
      C.sector(r,    1h-r, r, π/2,  π),
      C.sector(1w-r, 1h-r, r, 0,    π/2),
      C.stroke(nothing),
    ),
    C.compose(C.context(order=2),
      # Layer 2: stroke.
      C.line([
        [ (r, 0h), (1w-r, 0h) ],
        [ (0w, r), (0w, 1h-r) ],
        [ (r, 1h), (1w-r, 1h) ],
        [ (1w, r), (1w, 1h-r) ],
      ]),
      C.arc(r,    r,    r, π,    3π/2),
      C.arc(1w-r, r,    r, 3π/2, 0),
      C.arc(r,    1h-r, r, π/2,  π),
      C.arc(1w-r, 1h-r, r, 0,    π/2),
    ),
  )
end

""" Draw a continuous piecewise cubic Bezier curve in Compose.

The points are given by a vector [p1, c1, c2, p2, c3, c4, p3, ...] of length
3n+1 where n >=1 is the number of Bezier curves.
"""
function piecewise_curve(points::Vector{<:Tuple})
  @assert length(points) % 3 == 1
  C.compose(C.context(),
    (C.curve(points[i:i+3]...) for i in range(1, length(points)-1, step=3))...
  )
end

# Compose.jl properties
#######################

const default_props = Dict{Symbol,Vector{Compose.Property}}(
  :box => [ C.stroke("black"), C.fill(nothing) ],
  :junction => [ C.stroke("black") ],
  :variant_junction => [ C.stroke("black"), C.fill(nothing) ],
  :wire => [ C.stroke("black") ],
  :text => [ C.fill("black") ],
)

end

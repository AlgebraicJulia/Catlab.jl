""" Draw wiring diagrams using Compose.jl.
"""
module ComposeWiringDiagrams
export ComposePicture, to_composejl, to_composejl_context

import Compose
const C = Compose

using ...WiringDiagrams
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: position, size, lower_corner, upper_corner

# Constants and data types
##########################

const ComposeProperties = AbstractVector{Compose.Property}

# Default properties for root context, box context, and wire context.
const default_root_props = Compose.Property[
  C.font("Serif"),
  C.stroke("black"),
]
const default_box_props = Compose.Property[
  C.fill("transparent"),
]
const default_wire_props = Compose.Property[]

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

# Drawing
#########

""" Draw a wiring diagram in Compose.jl.
"""
function to_composejl(args...;
    base_unit::Compose.Measure=5*C.mm,
    root_props::ComposeProperties=default_root_props,
    box_props::ComposeProperties=default_box_props,
    wire_props::ComposeProperties=default_wire_props, kw...)::ComposePicture
  diagram = layout_diagram(args...; kw...)
  context = to_composejl_context(diagram;
    root_props=root_props, box_props=box_props, wire_props=wire_props)
  ComposePicture(context, (base_unit .* size(diagram))...)
end

""" Draw a wiring diagram in Compose.jl using the given layout.
"""
function to_composejl_context(diagram::WiringDiagram;
    root_props::ComposeProperties=default_root_props,
    box_props::ComposeProperties=default_box_props,
    wire_props::ComposeProperties=default_wire_props)::Compose.Context
  box_contexts = map(to_composejl_context, boxes(diagram))
  wire_contexts = map(wires(diagram)) do wire
    C.line([
      Tuple(abs_position(diagram, wire.source)),
      Tuple(abs_position(diagram, wire.target)),
    ])
  end
  # The origin of the Compose.jl coordinate system is in the top-left corner,
  # while the origin of wiring diagram layout is at the diagram center, so we
  # need to translate the coordinates using the `UnitBox`.
  C.compose(C.context(units=C.UnitBox(-size(diagram)/2..., size(diagram)...)),
    [C.context(); box_contexts; box_props],
    [C.context(); wire_contexts; wire_props],
    root_props...,
  )
end

function to_composejl_context(box::Box)::Compose.Context
  C.compose(C.context(lower_corner(box)..., size(box)..., units=C.UnitBox()),
    C.rectangle(),
    C.text(0.5, 0.5, string(box.value.value), C.hcenter, C.vcenter),
  )
end

function abs_position(diagram::WiringDiagram, port::Port)
  parent = port.box in (input_id(diagram), output_id(diagram)) ?
    diagram : box(diagram, port.box)
  position(parent) + position(port_value(diagram, port))
end

end

""" Draw wiring diagrams using Compose.jl.
"""
module ComposeWiringDiagrams
export ComposePicture, to_composejl, to_composejl_context

import Compose
const C = Compose

using ...WiringDiagrams
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: lower_corner

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

# Drawing
#########

""" Draw a wiring diagram in Compose.jl.
"""
function to_composejl(args...;
    base_unit::Compose.Measure=5*C.mm, kw...)::ComposePicture
  diagram = layout_diagram(args...; kw...)
  context = to_composejl_context(diagram)
  size = diagram.value.size
  ComposePicture(context, size[1] * base_unit, size[2] * base_unit)
end

""" Draw a wiring diagram in Compose.jl using the given layout.
"""
function to_composejl_context(diagram::WiringDiagram)::Compose.Context
  layout = diagram.value::BoxLayout
  C.compose(
    C.context(units=C.UnitBox(0, 0, layout.size...)),
    [C.context();
      [ C.rectangle(box) for box in boxes(diagram) ];
      C.fill("transparent"); C.stroke("black");
    ],
  )
end

Compose.rectangle(box::AbstractBox) = C.rectangle(box.value::BoxLayout)
Compose.rectangle(layout::BoxLayout) = 
  C.rectangle(lower_corner(layout)..., layout.size...)

end

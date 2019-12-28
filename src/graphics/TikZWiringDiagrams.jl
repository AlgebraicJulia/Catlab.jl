""" Draw wiring diagrams using TikZ.
"""
module TikZWiringDiagrams
export to_tikz, layout_to_tikz

using Compat
using DataStructures: OrderedDict
using Parameters
using StaticArrays: StaticVector, SVector

using ...Syntax: GATExpr, show_latex
using ...WiringDiagrams, ...WiringDiagrams.WiringDiagramSerialization
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: AbstractVector2D, Vector2D, BoxLayout, BoxShape,
  RectangleShape, CircleShape, JunctionShape, NoShape,
  position, normal, tangent, wire_points
import ..TikZ

# Data types
############

""" Internal data type for configurable options of Compose.jl wiring diagrams.
"""
@with_kw_noshow struct TikZOptions
  arrowtip::Union{String,Nothing} = nothing
  math_mode::Bool = true
  rounded_boxes::Bool = true
  props::Vector{TikZ.Property} = TikZ.Property[]
  styles::AbstractDict = Dict()
  libraries::Vector{String} = String[]
end

# Wiring diagrams
#################

""" Draw a wiring diagram in TikZ.
"""
function to_tikz(args...; kw...)
  layout_kw = filter(p -> first(p) ∉ fieldnames(TikZOptions), kw)
  diagram = layout_diagram(args...; layout_kw...)
  
  tikz_kw = filter(p -> first(p) ∈ fieldnames(TikZOptions), kw)
  layout_to_tikz(diagram; tikz_kw...)
end

""" Draw a wiring diagram in TikZ using the given layout.
"""
function layout_to_tikz(diagram::WiringDiagram; kw...)::TikZ.Picture
  layout_to_tikz(diagram, TikZOptions(; kw...))
end

function layout_to_tikz(diagram::WiringDiagram, opts::TikZOptions)
  stmts = tikz_box(diagram, Int[], opts)
  props = [
    [ TikZ.Property("x", "1em"), TikZ.Property("y", "1em") ];
    [ TikZ.Property("$name/.style", props)
      for (name, props) in merge(tikz_styles(opts), opts.styles) ];
    opts.props;
  ]
  libraries = [ opts.libraries; "calc" ]
  if !isnothing(opts.arrowtip)
    push!(props, TikZ.Property("decoration", 
      "{markings, mark=at position 0.5 with {\\arrow{$(opts.arrowtip)}}}"))
    append!(libraries, ["arrows.meta", "decorations.markings"])
  end
  TikZ.Picture(stmts...; props=props, libraries=unique!(libraries))
end

""" Make TikZ node for a box.
"""
function tikz_box(diagram::WiringDiagram, vpath::Vector{Int}, opts::TikZOptions)
  TikZ.Statement[
    tikz_node(diagram.value, opts, name=box_id(vpath), style="outer box");
    reduce(vcat, [ tikz_box(box(diagram, v), [vpath; v], opts)
                   for v in box_ids(diagram) ], init=[]);
    [ tikz_wire(diagram, wire, opts) for wire in wires(diagram) ];
  ]
end

function tikz_box(box::AbstractBox, vpath::Vector{Int}, opts::TikZOptions)
  TikZ.Statement[
    tikz_node(box.value::BoxLayout, opts; name=box_id(vpath))
  ]
end

function tikz_node(layout::BoxLayout, opts::TikZOptions;
    name::Union{String,Nothing}=nothing,
    style::Union{String,Nothing}=nothing)::TikZ.Node
  if isnothing(style)
    style = tikz_shapes[layout.shape]
  end
  content = layout.shape in tikz_content_shapes ?
    tikz_label(layout.value, opts) : ""
  TikZ.Node(name,
    props=[TikZ.Property(style); tikz_size(layout.size)],
    coord=tikz_coordinate(layout.position),
    content=content)
end

""" Make a TikZ edge/path for a wire.
"""
function tikz_wire(diagram::WiringDiagram, wire::Wire, opts::TikZOptions)::TikZ.Edge
  src, src_angle = tikz_port(diagram, wire.source)
  tgt, tgt_angle = tikz_port(diagram, wire.target)
  exprs, prev_angle = TikZ.PathExpression[ src ], src_angle
  for point in wire_points(wire)
    v = tangent(point)
    push!(exprs, TikZ.PathOperation("to"; props=[
      TikZ.Property("out", string(prev_angle)),
      TikZ.Property("in", string(tikz_angle(-v))),
    ]))
    push!(exprs, tikz_coordinate(position(point)))
    prev_angle = tikz_angle(v)
  end
  push!(exprs, TikZ.PathOperation("to"; props=[
    TikZ.Property("out", string(prev_angle)),
    TikZ.Property("in", string(tgt_angle)),
  ]))
  push!(exprs, tgt)
  TikZ.Edge(exprs...; props=[TikZ.Property("wire")])
end

""" Make TikZ coordinate and angle for a port.
"""
function tikz_port(diagram::WiringDiagram, port::Port)
  name = box_id(diagram, [port.box])
  parent_box = port.box in (input_id(diagram), output_id(diagram)) ?
    diagram : box(diagram, port.box)
  shape = parent_box.value.shape
  
  x, y = tikz_position(position(port_value(diagram, port)))
  normal_angle = tikz_angle(normal(diagram, port))
  anchor, (x, y) = if shape == RectangleShape
    nx, ny = normal(port_value(diagram, port))
    i = last(findmax((ny, nx, -ny, -nx)))
    anchor = ("north", "east", "south", "west")[i]
    (anchor, anchor in ("north", "south") ? (x,0) : (0,y))
  elseif shape in (CircleShape, JunctionShape)
    (normal_angle, (0,0))
  elseif shape == NoShape
    ("center", (0,0))
  else
    # Fallback method. Always works when TikZ follows the layout's box size, but
    # is the least robust to changes in node size.
    ("center", (x,y))
  end
  
  coord = if x == 0 && y == 0
    "$name.$anchor"
  else
    "\$($name.$anchor)+($(x)em,$(y)em)\$"
  end
  (TikZ.NodeCoordinate(coord), normal_angle)
end

function tikz_label(x, opts::TikZOptions)
  text = sprint(show, x)
  opts.math_mode ? string("\$", text, "\$") : text
end
function tikz_label(expr::GATExpr, opts::TikZOptions)
  if opts.math_mode
    string("\$", sprint(show_latex, expr), "\$")
  else
    sprint(show, expr)
  end
end
tikz_label(::Nothing, opts::TikZOptions) = ""

# TikZ geometry
###############

function tikz_angle(v::AbstractVector2D)
  tikz_number(rad2deg(angle(v[1] - v[2]*im)))
end

function tikz_position(position::AbstractVector2D)::Tuple
  # TikZ's default coordinate system has the positive y-axis going upwards.
  x, y = position
  (tikz_number(x), tikz_number(-y))
end
function tikz_coordinate(position::AbstractVector2D)::TikZ.Coordinate
  TikZ.Coordinate(tikz_position(position)...)
end

function tikz_size(size::AbstractVector2D)::Vector{TikZ.Property}
  width, height = tikz_number(size[1]), tikz_number(size[2])
  if width == 0 && height == 0
    TikZ.Property[]
  elseif width == height
    [ TikZ.Property("minimum size", "$(width)em") ]
  else
    [ TikZ.Property("minimum width", "$(width)em"), 
      TikZ.Property("minimum height", "$(height)em") ]
  end
end

function tikz_number(x::Number; sigdigits=3)
  x = round(x, sigdigits=sigdigits)
  isinteger(x) ? Integer(x) : x
end

# TikZ shapes and styles
########################

function tikz_styles(opts::TikZOptions)
  styles = OrderedDict(
    "outer box" => [
      TikZ.Property("draw", "none"),
    ],
    "box" => [
      TikZ.Property("rectangle"),
      TikZ.Property("draw"), TikZ.Property("solid"),
    ],
    "circular box" => [
      TikZ.Property("circle"),
      TikZ.Property("draw"), TikZ.Property("solid"),
    ],
    "junction" => [
      TikZ.Property("circle"),
      TikZ.Property("draw"), TikZ.Property("fill"),
      TikZ.Property("inner sep", "0"),
    ],
    "invisible" => [
      TikZ.Property("draw", "none"),
      TikZ.Property("inner sep", "0"),
    ],
    "wire" => [
      TikZ.Property("draw"),
    ],
  )
  if opts.rounded_boxes
    push!(styles["box"], TikZ.Property("rounded corners"))
  end
  if !isnothing(opts.arrowtip)
    push!(styles["wire"],
      TikZ.Property("postaction", [ TikZ.Property("decorate") ]))
  end
  styles
end

const tikz_shapes = Dict(
  RectangleShape => "box",
  CircleShape => "circular box",
  JunctionShape => "junction",
  NoShape => "invisible",
)
const tikz_content_shapes = Set([
  RectangleShape,
  CircleShape,
])

end

""" Draw wiring diagrams using TikZ.
"""
module TikZWiringDiagrams
export to_tikz, layout_to_tikz

using Compat
using DataStructures: OrderedDict
using Match
using Parameters

using ...Syntax: GATExpr, show_latex
using ...WiringDiagrams, ...WiringDiagrams.WiringDiagramSerialization
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: AbstractVector2D, Vector2D, BoxLayout, box_label,
  wire_label, position, normal, tangent, port_sign, wire_points
import ..WiringDiagramLayouts: svector
import ..TikZ

# Data types
############

""" Internal data type for configurable options of Compose.jl wiring diagrams.
"""
@with_kw_noshow struct TikZOptions
  orientation::LayoutOrientation = LeftToRight
  base_unit::String = "4mm"
  labels::Bool = false
  labels_pos::Union{String,Real} = 0.5
  math_mode::Bool = true
  arrowtip::Union{String,Nothing} = nothing
  arrowtip_pos::Union{String,Real} = 0.5
  rounded_boxes::Bool = true
  props::AbstractVector = ["semithick"]
  styles::AbstractDict = Dict()
  libraries::Vector{String} = String[]
  packages::Vector{String} = ["amssymb"]
  used_node_styles::AbstractSet = Set{String}()
end

svector(opts::TikZOptions, args...) = svector(opts.orientation, args...)

# Wiring diagrams
#################

""" Draw a wiring diagram in TikZ.
"""
function to_tikz(args...; orientation::LayoutOrientation=LeftToRight, kw...)
  layout_kw = filter(p -> first(p) ∉ fieldnames(TikZOptions), kw)
  diagram = layout_diagram(args...; orientation=orientation, layout_kw...)
  
  tikz_kw = filter(p -> first(p) ∈ fieldnames(TikZOptions), kw)
  layout_to_tikz(diagram; orientation=orientation, tikz_kw...)
end

""" Draw a wiring diagram in TikZ using the given layout.
"""
function layout_to_tikz(diagram::WiringDiagram; kw...)::TikZ.Document
  layout_to_tikz(diagram, TikZOptions(; kw...))
end

function layout_to_tikz(diagram::WiringDiagram, opts::TikZOptions)::TikZ.Document
  stmts = tikz_box(diagram, Int[], opts)
  styles, libraries = tikz_styles(opts)
  props = [
    [ # Define a unit length to be used for both TikZ coordinates and lengths.
      # https://tex.stackexchange.com/a/454598
      TikZ.Property("unit length/.code",
        "{{\\newdimen\\$tikz_unit_command}\\setlength{\\$tikz_unit_command}{#1}}"),
      TikZ.Property("unit length", opts.base_unit),
      TikZ.Property("x", "\\$tikz_unit_command"),
      TikZ.Property("y", "\\$tikz_unit_command") ];
    TikZ.as_properties(opts.props);
    [ TikZ.Property("$name/.style", TikZ.as_properties(props))
      for (name, props) in styles ];
  ]
  TikZ.Document(TikZ.Picture(stmts...; props=props);
    libraries=unique!([ "calc"; libraries; opts.libraries ]),
    packages=opts.packages)
end

""" Make TikZ node for a box.
"""
function tikz_box(diagram::WiringDiagram, vpath::Vector{Int}, opts::TikZOptions)
  layout = diagram.value::BoxLayout
  TikZ.Statement[
    TikZ.Node(box_id(vpath),
      props = [TikZ.Property("outer box"); tikz_size(layout.size)],
      coord = tikz_coordinate(layout.position),
    );
    reduce(vcat, [ tikz_box(box(diagram, v), [vpath; v], opts)
                   for v in box_ids(diagram) ], init=[]);
    [ tikz_edge(diagram, wire, opts) for wire in wires(diagram) ];
  ]
end

function tikz_box(box::AbstractBox, vpath::Vector{Int}, opts::TikZOptions)
  layout = box.value::BoxLayout
  style = tikz_node_style(layout, opts)
  TikZ.Statement[
    TikZ.Node(box_id(vpath),
      props = [TikZ.Property(style); tikz_size(layout.size)],
      coord = tikz_coordinate(layout.position),
      content = layout.shape in (:junction, :invisible) ? "" :
        tikz_node_label(layout.value, opts),
    ),
  ]
end

""" Make a TikZ edge/path for a wire.
"""
function tikz_edge(diagram::WiringDiagram, wire::Wire, opts::TikZOptions)::TikZ.Edge
  src, src_angle = tikz_port(diagram, wire.source, opts)
  tgt, tgt_angle = tikz_port(diagram, wire.target, opts)
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
  
  # Use source port for wire label, following the Graphviz wiring diagrams.
  src_layout = port_value(diagram, wire.source)
  tgt_layout = port_value(diagram, wire.target)
  label = opts.labels && src_layout.label_wires && tgt_layout.label_wires ?
    tikz_edge_label(src_layout.value, opts) : nothing
  props = [ TikZ.Property("wire", label) ]
  if !isnothing(opts.arrowtip)
    reversed = src_layout.reverse_wires && tgt_layout.reverse_wires
    push!(props, TikZ.Property(reversed ? "<-" : "->"))
  end
  
  TikZ.Edge(exprs...; props=props)
end

""" Make TikZ coordinate and angle for a port.
"""
function tikz_port(diagram::WiringDiagram, port::Port, opts::TikZOptions)
  name = box_id(diagram, [port.box])
  parent_box = port.box in outer_ids(diagram) ? diagram : box(diagram, port.box)
  shape = parent_box.value.shape
  
  x, y = tikz_position(position(port_value(diagram, port)))
  normal_angle = tikz_angle(normal(diagram, port))
  anchor, (x, y) = if shape in (:rectangle, :triangle, :invtriangle,
                                :trapezium, :invtrapezium)
    port_dir = svector(opts, port_sign(diagram, port, opts.orientation), 0)
    e2 = svector(opts, 0, 1)
    (tikz_anchor(port_dir), (e2[1]*x, e2[2]*y))
  elseif shape in (:circle, :ellipse, :junction)
    (normal_angle, (0,0))
  elseif shape == :invisible
    ("center", (0,0))
  else
    # Fallback method. Always works when TikZ follows the layout's box size, but
    # is the least robust to changes in node size.
    ("center", (x,y))
  end
  
  coord = if x == 0 && y == 0
    "$name.$anchor"
  else
    "\$($name.$anchor)+($x,$y)\$"
  end
  (TikZ.NodeCoordinate(coord), normal_angle)
end

function tikz_node_label(value, opts::TikZOptions)
  if opts.math_mode
    box_label(MIME("text/latex"), value)
  else
    escape_latex(box_label(MIME("text/plain"), value))
  end
end
function tikz_edge_label(value, opts::TikZOptions)
  if opts.math_mode
    wire_label(MIME("text/latex"), value)
  else
    escape_latex(wire_label(MIME("text/plain"), value))
  end
end

""" Escape special LaTeX characters.

Reference: https://tex.stackexchange.com/a/34586/
"""
function escape_latex(s::AbstractString)
  reduce(replace, [
    "\\" => "\\textbackslash",
    "~" => "\\textasciitilde",
    "^" => "\\textasciicircum",
    "&" => "\\&", "%" => "\\%", "\$" => "\\\$", "#" => "\\#",
    "_" => "\\_", "{" => "\\{", "}" => "\\}",
  ], init=s)
end

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
    [ TikZ.Property("minimum size", "$width\\$tikz_unit_command") ]
  else
    [ TikZ.Property("minimum width", "$width\\$tikz_unit_command"),
      TikZ.Property("minimum height", "$height\\$tikz_unit_command") ]
  end
end
const tikz_unit_command = "tikzunit"

tikz_anchor(v::AbstractVector2D) = tikz_anchors[Tuple(v)]

const tikz_anchors = Dict{Tuple{Int,Int},String}(
  (0,0)   => "center",
  (1,0)   => "east",
  (-1,0)  => "west",
  (0,1)   => "south",
  (0,-1)  => "north",
  (1,1)   => "south east",
  (-1,1)  => "south west",
  (1,-1)  => "north east",
  (-1,-1) => "north west",
)

function tikz_number(x::Number; digits=3)::Number
  x = round(x, digits=digits)
  isinteger(x) ? Integer(x) : x
end

# TikZ styles
#############

""" Make TikZ style definitions for wiring diagram.
"""
function tikz_styles(opts::TikZOptions)
  # Box style options.
  styles = OrderedDict(
    style => get(opts.styles, style) do; tikz_node_style(opts, style) end
    for style in sort!([["outer box", "wire"]; collect(opts.used_node_styles)])
  )
  libraries = [ "shapes.geometric" ] # FIXME: Should use library only if needed.
  
  # Wire style options.
  if opts.labels
    anchor = tikz_anchor(svector(opts, 0, 1))
    styles["wire"] = vcat(styles["wire"], tikz_decorate_markings([
      "at position $(opts.labels_pos) with {\\node[anchor=$anchor] {#1};}"
    ]))
    push!(libraries, "decorations.markings")
  end
  if !isnothing(opts.arrowtip)
    pos, arrowtip = opts.arrowtip_pos, opts.arrowtip
    merge!(styles, OrderedDict(
      "->" => tikz_decorate_markings([
        "at position $pos with {\\arrow{$arrowtip}}"
      ]),
      "<-" => tikz_decorate_markings([
        "at position $pos with {\\arrow{$arrowtip[reversed]}}"
      ]),
    ))
    append!(libraries, ["arrows.meta", "decorations.markings"])
  end
  
  (styles, libraries)
end

""" Get default TikZ style for given kind of node.
"""
function tikz_node_style(opts::TikZOptions, name::String)
  rounded = TikZ.Property(opts.rounded_boxes ? "rounded corners" : "sharp corners")
  @match name begin
    "outer box" => [
      TikZ.Property("draw", "none"),
    ]
    "wire" => [
      TikZ.Property("draw"),
    ]
    "box" => [
      TikZ.Property("rectangle"),
      TikZ.Property("draw"), TikZ.Property("solid"), rounded,
    ]
    "circular box" => [
      TikZ.Property("circle"),
      TikZ.Property("draw"), TikZ.Property("solid"),
    ]
    "elliptical box" => [
      TikZ.Property("ellipse"),
      TikZ.Property("draw"), TikZ.Property("solid"),
    ]
    "triangular box" => [
      TikZ.Property("isosceles triangle"),
      TikZ.Property("isosceles triangle stretches"),
      TikZ.Property("shape border rotate", Dict(
        # FIXME: Match.jl doesn't work with enums.
          LeftToRight => "180",
          RightToLeft => "0",
          TopToBottom => "90",
          BottomToTop => "270",
        )[opts.orientation]
      ),
      TikZ.Property("draw"), TikZ.Property("solid"), rounded,
      TikZ.Property("inner sep", "0"),
    ]
    "inverse triangular box" => [
      TikZ.Property("isosceles triangle"),
      TikZ.Property("isosceles triangle stretches"),
      TikZ.Property("shape border rotate", Dict(
          LeftToRight => "0",
          RightToLeft => "180",
          TopToBottom => "270",
          BottomToTop => "90",
        )[opts.orientation]
      ),
      TikZ.Property("draw"), TikZ.Property("solid"), rounded,
      TikZ.Property("inner sep", "0"),
    ]
    "trapezoidal box" => [
      TikZ.Property("trapezium"), TikZ.Property("trapezium angle", "80"),
      TikZ.Property("trapezium stretches body"),
      TikZ.Property("shape border rotate", Dict(
          LeftToRight => "90",
          RightToLeft => "270",
          TopToBottom => "0",
          BottomToTop => "180",
        )[opts.orientation]
      ),
      TikZ.Property("draw"), TikZ.Property("solid"), rounded,
    ]
    "inverse trapezoidal box" => [
      TikZ.Property("trapezium"), TikZ.Property("trapezium angle", "80"),
      TikZ.Property("trapezium stretches body"),
      TikZ.Property("shape border rotate", Dict(
          LeftToRight => "270",
          RightToLeft => "90",
          TopToBottom => "180",
          BottomToTop => "0",
        )[opts.orientation]
      ),
      TikZ.Property("draw"), TikZ.Property("solid"), rounded,
    ]
    "junction" => [
      TikZ.Property("circle"),
      TikZ.Property("draw"), TikZ.Property("fill"),
      TikZ.Property("inner sep", "0"),
    ]
    "variant junction" => [
      TikZ.Property("circle"),
      TikZ.Property("draw"), TikZ.Property("solid"),
      TikZ.Property("inner sep", "0"),
    ]
    "invisible" => [
      TikZ.Property("draw", "none"),
      TikZ.Property("inner sep", "0"),
    ]
    _ => TikZ.Property[]
  end
end

function tikz_decorate_markings(marks::Vector{TikZ.Property})
  [ TikZ.Property("postaction", [ TikZ.Property("decorate") ]),
    TikZ.Property("decoration", [ TikZ.Property("markings"); marks ]) ]
end
function tikz_decorate_markings(marks::Vector{String})
  tikz_decorate_markings([ TikZ.Property("mark", mark) for mark in marks ])
end

""" Get TikZ style for box.
"""
function tikz_node_style(layout::BoxLayout, opts::TikZOptions)
  style = if isnothing(layout.style)
    tikz_shapes[layout.shape]
  else
    replace(string(layout.style), "_" => " ")
  end
  push!(opts.used_node_styles, style)
  style
end

const tikz_shapes = Dict(
  :rectangle => "box",
  :circle => "circular box",
  :ellipse => "elliptical box",
  :triangle => "triangular box",
  :invtriangle => "inverse triangular box",
  :trapezium => "trapezoidal box",
  :invtrapezium => "inverse trapezoidal box",
  :junction => "junction",
  :invisible => "invisible",
)

end

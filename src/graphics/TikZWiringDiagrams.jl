""" Draw wiring diagrams using TikZ.
"""
module TikZWiringDiagrams
export to_tikz, layout_to_tikz

using Compat
using Parameters
using StaticArrays: StaticVector, SVector

using ...Syntax: GATExpr, show_latex
using ...WiringDiagrams, ...WiringDiagrams.WiringDiagramSerialization
using ..WiringDiagramLayouts
using ..WiringDiagramLayouts: AbstractVector2D, Vector2D, BoxLayout, BoxShape,
  RectangleShape, CircleShape, JunctionShape, NoShape
import ..TikZ

# Data types
############

""" Internal data type for configurable options of Compose.jl wiring diagrams.
"""
@with_kw_noshow struct TikZOptions
  math_mode::Bool = true
end

# Wiring diagrams
#################

""" Draw a wiring diagram in TikZ.
"""
function to_tikz(args...;
    arrowtip::Union{String,Nothing}=nothing,
    picture_props::Vector{TikZ.Property}=TikZ.Property[], kw...)
  layout_kw = filter(p -> first(p) ∉ fieldnames(TikZOptions), kw)
  diagram = layout_diagram(args...; layout_kw...)
  
  tikz_kw = filter(p -> first(p) ∈ fieldnames(TikZOptions), kw)
  stmts = layout_to_tikz(diagram; tikz_kw...)
  props = copy(picture_props)
  if !isnothing(arrowtip)
    push!(props, TikZ.Property("decoration", 
      "{markings, mark=at position 0.5 with {\\arrow{$arrowtip}}}"))
  end
  TikZ.Picture(stmts...; props=props)
end

""" Draw a wiring diagram in TikZ using the given layout.
"""
function layout_to_tikz(diagram::WiringDiagram; kw...)::Vector{<:TikZ.Statement}
  layout_to_tikz(diagram, TikZOptions(; kw...))
end

function layout_to_tikz(diagram::WiringDiagram, opts::TikZOptions)
  name(v::Int) = box_id(diagram, [v])
  stmts = TikZ.Statement[
    tikz_node(diagram, opts, name=name(input_id(diagram)), style="outer box");
    [ tikz_node(box(diagram, v), opts, name=name(v)) for v in box_ids(diagram) ]
  ]
  # TODO: Edges.
  stmts
end

function tikz_node(box::AbstractBox, opts::TikZOptions; kw...)
  tikz_node(box.value::BoxLayout, opts; kw...)
end
function tikz_node(layout::BoxLayout, opts::TikZOptions;
    name::Union{String,Nothing}=nothing, style::Union{String,Nothing}=nothing)
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

# TikZ helpers
##############

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

function tikz_position(position::AbstractVector2D)::AbstractVector2D
  # TikZ's default coordinate system has the positive y-axis going upwards.
  x, y = position
  SVector(x, -y)
end
function tikz_coordinate(position::AbstractVector2D)::TikZ.Coordinate
  TikZ.Coordinate(tikz_position(position)...)
end

function tikz_size(size::AbstractVector2D)::Vector{TikZ.Property}
  width, height = size
  if width == 0 && height == 0
    TikZ.Property[]
  elseif width == height
    [ TikZ.Property("minimum size", "$(width)em") ]
  else
    [ TikZ.Property("minimum width", "$(width)em"), 
      TikZ.Property("minimum height", "$(height)em") ]
  end
end

end

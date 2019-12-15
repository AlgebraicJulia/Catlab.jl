""" Backend-agnostic layout of wiring diagrams.

This module lays out morphism expressions as wiring diagrams, assigning
positions and sizes to all the boxes. It uses the structure of the morphism
expression to determine the layout. Thus, if you want to lay out an abstract
wiring diagram (of type `WiringDiagram`) you must first convert to it to an
expression, using `WiringDiagrams.to_hom_expr` or by some other means.
"""
module WiringDiagramLayouts
export LayoutOrientation, LeftToRight, RightToLeft, TopToBottom, BottomToTop,
  LayoutOptions, BoxLayout, layout_hom_expr

using AutoHashEquals
using Parameters
using StaticArrays: StaticVector, SVector, MVector

using ...Syntax
using ...Doctrines: ObExpr, HomExpr, dom, codom, compose, id, otimes, braid
using ...WiringDiagrams

# Data types
############

""" Orientation of wiring diagram.
"""
@enum LayoutOrientation LeftToRight RightToLeft TopToBottom BottomToTop

is_horizontal(orient::LayoutOrientation) = orient in (LeftToRight, RightToLeft)
is_vertical(orient::LayoutOrientation) = orient in (TopToBottom, BottomToTop)

""" Internal data type for configurable options of wiring diagram layout.
"""
@with_kw struct LayoutOptions
  orientation::LayoutOrientation = TopToBottom
  junctions::Bool = true
  base_box_size::Real = 2
  min_box_size::StaticVector{2,<:Real} = SVector(1, 1)
  sequence_pad::Real = 2
  parallel_pad::Real = 1
end

""" Layout for box in a wiring diagram.
"""
@auto_hash_equals struct BoxLayout{Value,T}
  value::Value
  position::MVector{2,T}
  size::MVector{2,T}
end

# Layout
########

""" Lay out a morphism expression as a wiring diagram.

Returns a wiring diagram with `BoxLayout`s assigned to every box in the diagram.

The layout is calculated with respect to a cartesian coordinate system with
origin in the top-left corner. Box positions are relative to their centers. All
positions and sizes are dimensionless (unitless).
"""
function layout_hom_expr(expr::HomExpr; kw...)::WiringDiagram
  opts = LayoutOptions(; kw...)
  layout_hom_expr(expr, opts)
end

function layout_hom_expr(expr::HomExpr, opts::LayoutOptions)
  # Default method: singleton diagram.
  inputs, outputs = collect(dom(expr)), collect(codom(expr))
  #size = 
  #layout = 
  singleton_diagram(Box(BoxLayout(expr, position, size), inputs, outputs))
end

function layout_hom_expr(expr::HomExpr{:compose}, opts::LayoutOptions)
  diagrams = [ layout_hom_expr(arg, opts) for arg in args(expr) ]
  dim = is_horizontal(opts.orientation) ? 1 : 2
  layout_sequential!(diagrams; dim=dim, pad=opts.sequence_pad)
  compose(diagrams)
end

function layout_hom_expr(expr::HomExpr{:otimes}, opts::LayoutOptions)
  diagrams = [ layout_hom_expr(arg, opts) for arg in args(expr) ]
  dim = is_vertical(opts.orientation) ? 1 : 2
  layout_sequential!(diagrams; dim=dim, pad=opts.parallel_pad)
  otimes(diagrams)
end

layout_hom_expr(expr::HomExpr{:id}, opts::LayoutOptions) = layout_wires(expr, opts)
layout_hom_expr(expr::HomExpr{:braid}, opts::LayoutOptions) = layout_wires(expr, opts)

function layout_wires(expr::HomExpr, opts::LayoutOptions)
  functor((Ports, WiringDiagram), expr;
    terms = Dict(
      :Ob => expr -> Ports([expr]),
      :Hom => expr -> error("Found morphism generator $expr during wire layout"),
    ))
end

""" Lay out a sequence of wiring diagrams one after the other.
"""
function layout_sequential!(diagrams::Vector{WiringDiagram};
                            dim::Int=1, pad::Real=0)
  @assert dim == 1 || dim == 2
  alt_dim = 3 - dim
  offset = pad
  for diagram in diagrams
    lower, upper = lower_corner(diagram), upper_corner(diagram)
    center = (lower + upper) / 2
    size = upper - lower
    for box in boxes(diagram)
      layout = box.value::BoxLayout
      # Offset along primary dimension.
      layout.position[dim] += (offset - lower[dim])
      # Re-center along alternate dimension. Has no effect if already centered.
      layout.position[alt_dim] -= center[alt_dim]
    end
    offset += size[dim] + pad
  end
end

function lower_corner(diagram::WiringDiagram)
  mapreduce((c,d) -> min.(c,d), boxes(diagram)) do box
    lower_corner(box.value)
  end
end
function upper_corner(diagram::WiringDiagram)
  mapreduce((c,d) -> max.(c,d), boxes(diagram)) do box
    upper_corner(box.value)
  end
end

lower_corner(layout::BoxLayout) = layout.position - layout.size/2
upper_corner(layout::BoxLayout) = layout.position + layout.size/2

end

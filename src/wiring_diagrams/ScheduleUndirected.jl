""" Scheduling and evaluation of undirected wiring diagrams.

In category-theoretic terms, this module is about evaluating arbitrary
composites of morphisms in hypergraph categories.
"""
module ScheduleUndirectedWiringDiagrams
export AbstractNestedUWD, AbstractUWDSchedule, NestedUWD, UWDSchedule,
  eval_nested_diagram, to_nested_diagram, sequential_schedule

using Compat: only

using ...Present, ...CategoricalAlgebra.CSets, ..UndirectedWiringDiagrams
using ..UndirectedWiringDiagrams: TheoryUWD, flat

const AbstractUWD = UndirectedWiringDiagram

# Data types
############

@present TheoryUWDSchedule <: TheoryUWD begin
  Composite::Ob

  parent::Hom(Composite, Composite)
  box_parent::Hom(Box, Composite)

  # Po-category axiom enforcing that composites form a rooted forest.
  # parent <= id(Composite)
end

const AbstractUWDSchedule = AbstractACSetType(TheoryUWDSchedule)

""" TODO
"""
const UWDSchedule = CSetType(TheoryUWDSchedule,
  index=[:box, :junction, :outer_junction, :parent, :box_parent])


@present TheoryNestedUWD <: TheoryUWDSchedule begin
  CompositePort::Ob

  composite::Hom(CompositePort, Composite)
  composite_junction::Hom(CompositePort, Junction)
end

const AbstractNestedUWD = AbstractACSetType(TheoryNestedUWD)

""" TODO
"""
const NestedUWD = CSetType(TheoryNestedUWD,
  index=[:box, :junction, :outer_junction,
         :composite, :composite_junction, :parent, :box_parent])

const AbstractUWDForest = Union{AbstractUWDSchedule,AbstractNestedUWD}

composites(x::AbstractUWDForest) = parts(x, :Composite)
parent(x::AbstractUWDForest, args...) = subpart(x, args..., :parent)
children(x::AbstractUWDForest, args...) = incident(x, args..., :parent)
box_parent(x::AbstractUWDForest, args...) = subpart(x, args..., :box_parent)
box_children(x::AbstractUWDForest, args...) = incident(x, args..., :box_parent)

composite_ports(d::AbstractNestedUWD, args...) =
  incident(d, args..., :composite)
composite_ports_with_junction(d::AbstractNestedUWD, args...) =
  incident(d, args..., :composite_junction)
composite_junction(d::AbstractNestedUWD, args...) =
  subpart(d, args..., :composite_junction)

# Evaluation
############

""" TODO
"""
function eval_nested_diagram(f, d::AbstractNestedUWD, generators::AbstractVector)
  function eval_composite(c::Int)
    bs, cs = box_children(d, c), children(d, c)
    values = [ generators[bs]; map(eval_composite, cs) ]
    js = [ [junction(d, ports(d, b)) for b in bs];
           [composite_junction(d, composite_ports(d, c′)) for c′ in cs] ]
    outgoing_js = composite_junction(d, composite_ports(d, c))
    f(values, js, outgoing_js)
  end

  roots = filter(c -> parent(d, c) == c, composites(d))
  eval_composite(only(roots))
end

""" TODO
"""
function to_nested_diagram(s::AbstractUWDSchedule)
  d = NestedUWD()
  copy_parts!(d, s)

  function add_composite_ports!(c::Int)
    # Recursively add ports to all child composites.
    foreach(add_composite_ports!, children(d, c))

    # Get all junctions incident to any child box or child composite.
    c_box_ports = flat([ports(d, b) for b in box_children(d, c)])
    c_composite_ports = flat([composite_ports(d, c′) for c′ in children(d, c)])
    js = unique!([ junction(d, c_box_ports);
                   composite_junction(d, c_composite_ports) ])

    # Filter for "outgoing" junctions, having incident ports outside this node.
    c_box_ports, c_composite_ports = Set(c_box_ports), Set(c_composite_ports)
    js = filter!(js) do j
      !(ports_with_junction(d, j) ⊆ c_box_ports &&
        composite_ports_with_junction(d, j) ⊆ c_composite_ports &&
        isempty(ports_with_junction(d, j, outer=true)))
    end

    # Add port for each outgoing junction.
    add_parts!(d, :CompositePort, length(js), composite=c, composite_junction=js)
  end

  # Add ports to each composite, starting at roots.
  roots = filter(c -> parent(d, c) == c, composites(d))
  foreach(add_composite_ports!, roots)

  return d
end

# Scheduling
############

""" Schedule UWD as a sequential chain of binary composites.
"""
sequential_schedule(d::AbstractUWD) = sequential_schedule(d, boxes(d))

function sequential_schedule(d::AbstractUWD, boxes::AbstractVector{Int})
  nb = nboxes(d)
  @assert length(boxes) == nb
  nc = max(1, nb-1)

  schedule = UWDSchedule()
  copy_parts!(schedule, d)
  add_parts!(schedule, :Composite, nc, parent=[2:nc; nc])
  set_subpart!(schedule, boxes[1:min(2,nb)], :box_parent, 1)
  set_subpart!(schedule, boxes[3:nb], :box_parent, 2:nc)
  schedule
end

end

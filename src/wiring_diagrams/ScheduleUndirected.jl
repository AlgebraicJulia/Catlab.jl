""" Scheduling and evaluation of undirected wiring diagrams.

In category-theoretic terms, this module is about evaluating arbitrary
composites of morphisms in hypergraph categories.
"""
module ScheduleUndirectedWiringDiagrams
export AbstractNestedUWD, AbstractUWDSchedule, NestedUWD, UWDSchedule,
  eval_schedule, to_nested_diagram, sequential_schedule

using Compat: only
using DataStructures: IntDisjointSets, union!, in_same_set

using ...Present, ...CategoricalAlgebra.CSets, ...CategoricalAlgebra.FinSets
using ..UndirectedWiringDiagrams
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

""" Schedule of an undirected wiring diagram.

A schedule consists of a UWD together a set of *composites* forming a rooted
tree, or in general a rooted forest, whose leaves are the diagram's boxes.
"""
const UWDSchedule = CSetType(TheoryUWDSchedule,
  index=[:box, :junction, :outer_junction, :parent, :box_parent])

ncomposites(x::AbstractACSet) = nparts(x, :Composite)
composites(x::AbstractACSet) = parts(x, :Composite)
parent(x::AbstractACSet, args...) = subpart(x, args..., :parent)
children(x::AbstractACSet, c::Int) =
  filter(c′ -> c′ != c, incident(x, c, :parent))
box_parent(x::AbstractACSet, args...) = subpart(x, args..., :box_parent)
box_children(x::AbstractACSet, args...) = incident(x, args..., :box_parent)

@present TheoryNestedUWD <: TheoryUWDSchedule begin
  CompositePort::Ob

  composite::Hom(CompositePort, Composite)
  composite_junction::Hom(CompositePort, Junction)
end

const AbstractNestedUWD = AbstractACSetType(TheoryNestedUWD)

""" Nested undirected wiring diagram.

A nested UWD is a scheduled UWD whose composite nodes have been given ports,
making explicit the intermediate boxes in the composition.
"""
const NestedUWD = CSetType(TheoryNestedUWD,
  index=[:box, :junction, :outer_junction,
         :composite, :composite_junction, :parent, :box_parent])

composite_ports(x::AbstractACSet, args...) = incident(x, args..., :composite)
composite_junction(x::AbstractACSet, args...) =
  subpart(x, args..., :composite_junction)
composite_ports_with_junction(x::AbstractACSet, args...) =
  incident(x, args..., :composite_junction)

# Evaluation
############

""" Evaluate a scheduled UWD given a set of generators for the boxes.

The first argument `f` is a function that should support the signature

```
f(values::AbstractVector,
  juncs::AbstractVector{<:FinFunction{Int}},
  outer_junc::FinFunction{Int})
```

where `values` is a list of generators corresponding to the atomic boxes of the
diagram; `juncs` is an equal-length list of `FinSet` functions, mapping the
ports of the generators to junctions; and `outer_junc` is a `FinSet` function
mapping the outer ports to junctions.

Nested UWDs are used as an intermediate data structure during the evaluation. If
the schedule will be evaluated multiple times, you should explicitly convert the
schedule to a nested UWD using [`to_nested_diagram`](@ref) and then call
`eval_schedule` on the resulting object instead.
"""
eval_schedule(f, s::AbstractUWDSchedule, generators::AbstractVector) =
  eval_schedule(f, to_nested_diagram(s), generators)

function eval_schedule(f, d::AbstractNestedUWD, generators::AbstractVector)
  # Evaluate `f` after normalizing junctions to consecutive numbers 1:n.
  # Question: Should this normalization be optional? It's convenient but also
  # has some (small) cost.
  function do_eval(values, juncs, outer_junc)
    jmap = Dict{Int,Int}()
    for j in Iterators.flatten((Iterators.flatten(juncs), outer_junc))
      get!(jmap, j) do; length(jmap) + 1 end
    end
    njunc = length(jmap)
    f(values, map(js -> FinFunction([jmap[j] for j in js], njunc), juncs),
      FinFunction([jmap[j] for j in outer_junc], njunc))
  end

  # Mutually recursively evaluate children of composite `c`.
  function eval_children(c::Int)
    bs, cs = box_children(d, c), children(d, c)
    values = [ generators[bs]; map(eval_composite, cs) ]
    juncs = [ [junction(d, ports(d, b)) for b in bs];
              [composite_junction(d, composite_ports(d, c′)) for c′ in cs] ]
    (values, juncs)
  end

  # Mutually recursively evaluate composite `c`.
  function eval_composite(c::Int)
    values, juncs = eval_children(c)
    outer_junc = composite_junction(d, composite_ports(d, c))
    do_eval(values, juncs, outer_junc)
  end

  # Evaluate diagram starting at the root, assumed to be unique. The root
  # composite must be handled specially due to outer ports.
  root = only(filter(c -> parent(d, c) == c, composites(d)))
  values, juncs = eval_children(root)
  do_eval(values, juncs, junction(d, outer=true))
end

""" Convert a scheduled UWD to a nested UWD.
"""
function to_nested_diagram(s::AbstractUWDSchedule)
  d = NestedUWD()
  copy_parts!(d, s)

  n = nboxes(s)
  sets = IntDisjointSets(n + ncomposites(s))

  function add_composite_ports!(c::Int)
    # Recursively add ports to all child composites.
    foreach(add_composite_ports!, children(d, c))

    # Get all junctions incident to any child box or child composite.
    js = unique!(sort!(flat([
      [ junction(d, ports(d, b)) for b in box_children(d, c) ];
      [ composite_junction(d, composite_ports(d, c′)) for c′ in children(d, c) ]
    ])))

    # Filter for "outgoing" junctions, namely those incident to an outer port or
    # to a port of a box that is not a descendant of this composite.
    c_rep = n+c
    for b in box_children(d, c); union!(sets, c_rep, b) end
    for c′ in children(d, c); union!(sets, c_rep, n+c′) end
    js = filter!(js) do j
      !(all(in_same_set(sets, c_rep, box(d, port))
            for port in ports_with_junction(d, j)) &&
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

This is the simplest possible scheduling algorithm, the equivalent of `foldl`
for undirected wiring diagrams. Unless otherwise specified, the boxes are folded
in according to the (arbitrary) order of their IDs.
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

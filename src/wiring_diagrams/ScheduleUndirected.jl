""" Scheduling and evaluation of undirected wiring diagrams.

In category-theoretic terms, this module is about evaluating arbitrary
composites of morphisms in hypergraph categories.
"""
module ScheduleUndirectedWiringDiagrams
export AbstractNestedUWD, AbstractScheduledUWD, NestedUWD, ScheduledUWD,
  SchedulingAlgorithm, SequentialSchedule,
  eval_schedule, to_nested_diagram, schedule

import Base: schedule
using DataStructures: IntDisjointSets, union!, in_same_set

using ...Present, ...CategoricalAlgebra.CSets, ...CategoricalAlgebra.FinSets
using ..UndirectedWiringDiagrams, ..WiringDiagramAlgebras
using ..UndirectedWiringDiagrams: flat

# Data types
############

""" Abstract type for C-sets that contain a scheduled UWDS.

This type includes [`ScheduledUWD`](@ref) and [`NestedUWD`](@ref).
"""
@abstract_acset_type HasScheduledUWD <: HasUWD

@present SchScheduledUWD <: SchUWD begin
  Composite::Ob

  parent::Hom(Composite, Composite)
  box_parent::Hom(Box, Composite)

  # Po-category axiom enforcing that composites form a rooted forest.
  # parent <= id(Composite)
end

@abstract_acset_type AbstractScheduledUWD <: HasScheduledUWD

""" Scheduled undirected wiring diagram.

A scheduled UWD consists of a UWD together with a set of *composite* nodes
forming a rooted tree, or in general a rooted forest, whose leaves are the
diagram's boxes.

See also: [`NestedUWD`](@ref).
"""
@acset_type ScheduledUWD(SchScheduledUWD,
  index=[:box, :junction, :outer_junction, :parent, :box_parent]) <: AbstractScheduledUWD

ncomposites(x::HasScheduledUWD) = nparts(x, :Composite)
composites(x::HasScheduledUWD) = parts(x, :Composite)
parent(x::HasScheduledUWD, args...) = subpart(x, args..., :parent)
children(x::HasScheduledUWD, c::Int) =
  filter(c′ -> c′ != c, incident(x, c, :parent))
box_parent(x::HasScheduledUWD, args...) = subpart(x, args..., :box_parent)
box_children(x::HasScheduledUWD, args...) = incident(x, args..., :box_parent)

""" Abstract type for C-sets that contained a nested UWD.
"""
@abstract_acset_type HasNestedUWD <: HasScheduledUWD

@present SchNestedUWD <: SchScheduledUWD begin
  CompositePort::Ob

  composite::Hom(CompositePort, Composite)
  composite_junction::Hom(CompositePort, Junction)
end

@abstract_acset_type AbstractNestedUWD <: HasNestedUWD

""" Nested undirected wiring diagram.

A nested UWD is a scheduled UWD whose composite nodes have been given ports,
making explicit the intermediate boxes in the composition.

Nested UWDs are very similar but not quite identical to Robin Milner's
[bigraphs](https://doi.org/10.1017/CBO9780511626661).

See also: [`ScheduledUWD`](@ref).
"""
@acset_type NestedUWD(SchNestedUWD,
  index=[:box, :junction, :outer_junction,
         :composite, :composite_junction, :parent, :box_parent]) <: AbstractNestedUWD

composite_ports(x::HasNestedUWD, args...) = incident(x, args..., :composite)
composite_junction(x::HasNestedUWD, args...) =
  subpart(x, args..., :composite_junction)
composite_ports_with_junction(x::HasNestedUWD, args...) =
  incident(x, args..., :composite_junction)

# Evaluation
############

""" Evaluate a scheduled UWD given a set of generators for the boxes.

The optional first argument `f` should be a callable with the same signature as
[`oapply`](@ref) for UWD algebras, which by default is `oapply` itself.

```julia
f(composite::UndirectedWiringDiagram, values::AbstractVector)
```

Nested UWDs are used as an auxiliary data structure during the evaluation. If
the schedule will be evaluated multiple times, you should explicitly convert it
to a nested UWD using [`to_nested_diagram`](@ref) and then call `eval_schedule`
on the resulting object instead.
"""
eval_schedule(schedule, generators::AbstractVector) =
  eval_schedule(oapply, schedule, generators)

eval_schedule(f, schedule::AbstractScheduledUWD, generators::AbstractVector) =
  eval_schedule(f, to_nested_diagram(schedule), generators)

function eval_schedule(f, d::AbstractNestedUWD, generators::AbstractVector)
  # Evaluate `f` after constructing UWD for the composite.
  function do_eval(values, juncs, outer_junc)
    # Create diagram, adding boxes and ports.
    composite = UndirectedWiringDiagram(length(outer_junc))
    for junc in juncs
      add_box!(composite, length(junc))
    end

    # Set junctions, normalizing junction IDs to consecutive numbers `1:n`.
    jmap = Dict{Int,Int}()
    mapj!(j) = get!(jmap, j) do; add_junction!(composite) end
    for (port, j) in enumerate(Iterators.flatten(juncs))
      set_subpart!(composite, port, :junction, mapj!(j))
    end
    for (port, j) in enumerate(outer_junc)
      set_subpart!(composite, port, :outer_junction, mapj!(j))
    end

    f(composite, values)
  end

  # Mutually recursively evaluate children of composite `c`.
  function eval_children(c::Int)
    bs, cs = box_children(d, c), children(d, c)
    values = isempty(cs) ? generators[bs] : # XXX: Avoid Any[].
      [ generators[bs]; map(eval_composite, cs) ]
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
function to_nested_diagram(s::AbstractScheduledUWD)
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

    # Filter for "outgoing" junctions, namely those incident to any outer port
    # or to any port of a box that is not a descendant of this composite.
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

abstract type SchedulingAlgorithm end

""" Schedule diagram as a sequential chain of binary composites.

This is the simplest possible scheduling algorithm, the equivalent of `foldl`
for undirected wiring diagrams. Unless otherwise specified, the boxes are folded
according to the order of their IDs, which is arbitrary.
"""
struct SequentialSchedule <: SchedulingAlgorithm end

""" Schedule an undirected wiring diagram.

By default, a simple sequential schedule is used.
"""
function schedule(d::AbstractUWD;
                  alg::SchedulingAlgorithm=SequentialSchedule(), kw...)
  schedule(d, alg; kw...)
end

function schedule(d::AbstractUWD, ::SequentialSchedule;
                  order::Union{AbstractVector{Int},Nothing}=nothing)
  if isnothing(order)
    order = boxes(d)
  end
  nb = nboxes(d)
  @assert length(order) == nb
  nc = max(1, nb-1)

  schedule = ScheduledUWD()
  copy_parts!(schedule, d)
  add_parts!(schedule, :Composite, nc, parent=[2:nc; nc])
  set_subpart!(schedule, order[1:min(2,nb)], :box_parent, 1)
  set_subpart!(schedule, order[3:nb], :box_parent, 2:nc)
  schedule
end

end

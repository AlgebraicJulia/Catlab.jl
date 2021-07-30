""" Sketched C-sets are a data structure for models of sketches.

A *sketch* is a presentation of a category ``C`` together with a set of cones
and a set of cocones. A *model* of a sketch is a ``C``-set such that all the
cones are limit cones and all the cocones are limit cocones. This module
provides a data structure for models of finite limit sketches. Colimits are not
yet supported.

A *sketched C-set* consists of an underlying C-set, provided by the module
[`Catlab.CSets`](@ref), and a finite limit sketch. The sketched C-set data
structure is responsible for ensuring that at all times the specified cones are
in fact limit cones. The user may set any parts and subparts that do not belong
to a cone using the usual interface for C-sets. The cones are automatically and
incrementally updated in response to these changes. Directly modifying parts or
subparts belonging to cones is not permitted.

Sketches are a well-established concept in category theory, described at length
in the books by Barr and Wells (*Category Theory for Computing Science* and
*Toposes, Triples, and Theories*). However, our philosophy departs slightly from
the usual one. One would usually include whichever cones are needed to specify
both the operations and the axioms of the theory. In practice, computing limits
needed only for axioms is wasteful and so we would not specify such cones. For
example, the theory of categories, a classic example of a finite limit sketch,
has a binary pullback for the composition operation and a ternary limit for the
associativity axiom. In a sketched C-set for finite categories, we would include
only the pullback.
"""
module SketchedACSets
export SketchedACSet

using StaticArrays: SVector

using ...Present, ...Syntax, ...Theories
using ...Graphs, ..Limits, ..FinSets, ..CSets
using ...Graphs.BasicGraphs: TheoryReflexiveGraph
using ..FreeDiagrams: allequal
import ...Theories: ob, hom
import ..CSets: nparts, parts, subpart, incident, has_part, has_subpart,
  add_part!, add_parts!, set_subpart!, set_subparts!

# Sketches
##########

@present TheorySketchGraph <: TheoryReflexiveGraph begin
  Name::Data
  ob::Attr(V,Name)
  hom::Attr(E,Name)
end

@present TheorySketch <: TheorySketchGraph begin
  Op::Ob
  out_vertex::Hom(Op,V)

  (In, Out)::Ob
  op_in::Hom(In,Op)
  op_out::Hom(Out,Op)
  in_edge::Hom(In,E)
  out_edge::Hom(Out,E)
end

""" A combinatorial data structure for a sketch.

The generating objects and morphisms form a reflexive graph. The dependencies
between morphisms are encoded by a directed hypergraph whose vertices are the
graph edges and whose hyperedges are called "operations." Because the graph is
reflexive, the inputs and outputs of the operations can be objects or morphisms.
For now, all the operations are limits, with the outputs of each operation
comprising a cone. However, little about this data structure is specific to
limits or colimits and in the future we may consider other kinds of operations.
"""
const Sketch = ACSetType(TheorySketch,
  # FIXME: `out_vertex` and `out_edge` should be uniquely indexed.
  index=[:src, :tgt, :refl, :out_vertex, :op_in, :op_out, :in_edge, :out_edge],
  unique_index=[:ob, :hom])

function Sketch(pres::Presentation{SchemaType,Name}) where {SchemaType,Name}
  sketch = Sketch{Name}()
  add_graph_elements!(sketch, pres)
  add_limit_ops!(sketch, pres)
  sketch
end

ob(sketch::Sketch, args...) = subpart(sketch, args..., :ob)
hom(sketch::Sketch, args...) = subpart(sketch, args..., :hom)
ob_vertex(sketch::Sketch, args...) = incident(sketch, args..., :ob)
hom_edge(sketch::Sketch, args...) = incident(sketch, args..., :hom)

out_vertex(sketch::Sketch, args...) = subpart(sketch, args..., :out_vertex)
in_edge(sketch::Sketch, args...) = subpart(sketch, args..., :in_edge)
out_edge(sketch::Sketch, args...) = subpart(sketch, args..., :out_edge)
op_inputs(sketch::Sketch, op::Int) = incident(sketch, op, :op_in)
op_outputs(sketch::Sketch, op::Int) = incident(sketch, op, :op_out)

""" Add objects and morphisms of presentation as vertices and edges in sketch.
"""
function add_graph_elements!(sketch::Sketch, pres::Presentation)
  # Add objects and identity morphisms.
  obs = generators(pres, :Ob)
  vs = add_parts!(sketch, :V, length(obs), ob=map(first, obs))
  es = add_parts!(sketch, :E, length(obs), src=vs, tgt=vs, hom=sketch[vs,:ob])
  set_subpart!(sketch, vs, :refl, es)

  # Add morphism generators.
  homs = generators(pres, :Hom)
  add_parts!(sketch, :E, length(homs),
             src = ob_vertex(sketch, map(first∘dom, homs)),
             tgt = ob_vertex(sketch, map(first∘codom, homs)),
             hom = map(first, homs))
end

""" Add finite limits of presentation as operations in sketch.
"""
function add_limit_ops!(sketch::Sketch, pres::Presentation)
  for expr in generators(pres)
    gat_type = gat_typeof(expr)
    gat_type ∈ (:Ob, :Hom, :Data, :Attr) && continue
    add_op!(sketch, Val{gat_type}, expr)
  end
end

add_op!(sketch::Sketch, ::Type{Val{:Terminal}}, term) =
  add_op!(sketch, ob(term), [], [])

add_op!(sketch::Sketch, ::Type{Val{:Product}}, prod) = begin
  π1, π2 = proj1(prod), proj2(prod)
  add_op!(sketch, ob(prod), [codom(π1), codom(π2)], [π1, π2])
end

add_op!(sketch::Sketch, ::Type{Val{:Equalizer}}, eq) =
  add_op!(sketch, ob(eq), [left(eq), right(eq)], [incl(eq)])

add_op!(sketch::Sketch, ::Type{Val{:Pullback}}, pb) =
  add_op!(sketch, ob(pb), [left(pb), right(pb)], [proj1(pb), proj2(pb)])

function add_op!(sketch::Sketch, out, inputs, outputs)
  op = add_part!(sketch, :Op, out_vertex=ob_vertex(sketch, coerce_arg(out)))
  add_parts!(sketch, :In, length(inputs), op_in=op,
             in_edge=hom_edge(sketch, map(coerce_arg, inputs)))
  add_parts!(sketch, :Out, length(outputs), op_out=op,
             out_edge=hom_edge(sketch, map(coerce_arg, outputs)))
  op
end
coerce_arg(x::GATExpr) = first(x)
coerce_arg(x) = x

""" Topological sort of the operations in a sketch.
"""
function topological_sort_ops(sketch::Sketch; kw...)
  # XXX: The graph is a left pushforward data migration, but to avoid overhead
  # we'll do it manually. We should have a static version of data migration.
  g = Graph()
  add_vertices!(g, nparts(sketch, :Op))
  extra_vs = add_vertices!(g, nparts(sketch, :E))
  add_edges!(g, extra_vs[sketch[:in_edge]], sketch[:op_in])
  add_edges!(g, sketch[:op_out], extra_vs[sketch[:out_edge]])

  filter(<=(nparts(sketch, :Op)), topological_sort(g; kw...))
end

# Sketched C-sets
#################

""" A sketched, attributed C-set.

This data structure is an attributed C-set that is also a model of a sketch. It
supports the usual imperative interface for acsets except that destructive
mutations are currently not supported: parts cannot be removed and subparts that
have been assigned (are nonnull) cannot be unassigned or reassigned.
"""
struct SketchedACSet{ACS<:AbstractACSet}
  sketch::Sketch
  acset::ACS

  function SketchedACSet(sketch::Sketch, acset::ACS) where {ACS <: AbstractACSet}
    X = new{ACS}(sketch, acset)
    initialize_ops!(X)
    return X
  end
end

SketchedACSet(schema::Presentation, acset::AbstractACSet) =
  SketchedACSet(Sketch(schema), acset)

# Accessors just delegate to the underlying acset.
@inline nparts(X::SketchedACSet, args...) = nparts(X.acset, args...)
@inline parts(X::SketchedACSet, args...) = parts(X.acset, args...)
@inline subpart(X::SketchedACSet, args...) = subpart(X.acset, args...)
@inline incident(X::SketchedACSet, args...) = incident(X.acset, args...)
@inline has_part(X::SketchedACSet, args...) = has_part(X.acset, args...)
@inline has_subpart(X::SketchedACSet, args...) = has_subpart(X.acset, args...)

@inline Base.getindex(X::SketchedACSet, args...) = subpart(X, args...)
@inline Base.setindex!(X::SketchedACSet, value, args...) =
  set_subpart!(X, args..., value)

add_part!(X::SketchedACSet, ob::Symbol, args...; kw...) =
  only(add_parts!(X, ob, 1, args...; kw...))

function add_parts!(X::SketchedACSet, ob::Symbol, n::Int, args...; kw...)
  isempty(incident(X.sketch, ob_vertex(X.sketch, ob), :out_vertex)) ||
    error("$ob is a derived object; it cannot be directly mutated")
  parts = _add_parts(X, ob, n)
  set_subparts!(X, parts, args...; kw...)
  parts
end

""" Add parts to underlying acset, then propagate updates.
"""
function _add_parts(X::SketchedACSet, ob::Symbol, n::Int)
  n > 0 || return 1:0
  old_parts = parts(X.acset, ob)
  new_parts = add_parts!(X.acset, ob, n)
  propagate_updates!(X, ob, old_parts, new_parts)
  new_parts
end

set_subparts!(X::SketchedACSet, parts; kw...) = for pair in kw
  set_subpart!(X, parts, pair...) end
set_subparts!(X::SketchedACSet, parts, subparts) = for pair in pairs(subparts)
  set_subpart!(X, parts, pair...) end

function set_subpart!(X::SketchedACSet, parts, hom::Symbol, subparts)
  isempty(incident(X.sketch, hom_edge(X.sketch, hom), :out_edge)) ||
    error("$hom is a derived morphism; it cannot be directly mutated")
  all(==(0), subpart(X.acset, parts, hom)) ||
    error("$hom already defined at element(s) in $parts; it cannot be mutated")
  _set_subpart!(X, parts, hom, subparts)
end

""" Set subparts in underlying acset, then propagate updates.
"""
function _set_subpart!(X::SketchedACSet, new_parts, hom::Symbol, subparts)
  !isempty(new_parts) || return
  old_parts = findall(!=(0), subpart(X.acset, hom))
  set_subpart!(X.acset, new_parts, hom, subparts)
  propagate_updates!(X, hom, old_parts, new_parts)
end

""" Evaluate all operations on initial data.
"""
function initialize_ops!(X::SketchedACSet)
  # XXX: We want a C-poset: the topological order should be part of the data of
  # the sketch so we don't have to recompute or cache it. Alternatively, in a
  # static version of sketched C-sets, this would be done once at compile time.
  for op in topological_sort_ops(X.sketch)
    initialize_op!(X, op)
  end
end
function initialize_op!(X::SketchedACSet, op::Int)
  apex_name = ob(X.sketch, out_vertex(X.sketch, op))
  nparts(X.acset, apex_name) == 0 ||
    error("$apex_name is a derived object, but it already has elements")

  # Compute limit cone.
  args = map(op_inputs(X.sketch, op)) do input
    total_function(X.acset, hom(X.sketch, in_edge(X.sketch, input)))
  end
  lim = limit_op(X, op, args)

  # Add limit cone to underlying acset, without propagating updates.
  apex_parts = add_parts!(X.acset, apex_name, length(ob(lim)))
  for (o, leg) in zip(op_outputs(X.sketch, op), legs(lim))
    leg_name = hom(X.sketch, out_edge(X.sketch, o))
    set_subpart!(X.acset, apex_parts, leg_name, collect(leg))
  end
end

""" Evaluate operations that dependent on new data.

This can recursively trigger further updates.
"""
function propagate_updates!(X::SketchedACSet, name::Symbol, old_parts, new_parts)
  f_old = total_function(X.acset, name, coerce_vector(old_parts))
  f_new = total_function(X.acset, name, coerce_vector(new_parts))

  # Update all limits depending on this object or morphism.
  edge = hom_edge(X.sketch, name)
  for input in incident(X.sketch, edge, :in_edge)
    # Compute limit cone using only the new values for this input and taking the
    # old or current values at all other inputs. This tricky logic is based on
    # the distributivity of limits over coproducts in Set.
    op = X.sketch[input, :op_in]
    args = map(op_inputs(X.sketch, op)) do i
      e = in_edge(X.sketch, i)
      if i == input; f_new
      elseif i > input && e == edge; f_old
      else total_function(X.acset, hom(X.sketch, e)) end
    end
    lim = limit_op(X, op, args)

    # Add limit cone to underlying acset, reindexing the new elements and
    # propagating more updates as needed.
    apex_name = ob(X.sketch, out_vertex(X.sketch, op))
    apex_parts = _add_parts(X, apex_name, length(ob(lim)))
    for (i, o, leg) in zip(op_inputs(X.sketch, op), op_outputs(X.sketch, op), legs(lim))
      leg_name = hom(X.sketch, out_edge(X.sketch, o))
      # FIXME: This condition for reindexing will not work for equalizers.
      leg_values = i == input ? new_parts[collect(leg)] : collect(leg)
      _set_subpart!(X, apex_parts, leg_name, leg_values)
    end
  end
end
coerce_vector(x::AbstractVector) = x
coerce_vector(x::Int) = x:x

""" Compute limit associated with operation with given arguments.

XXX: The manual dispatch based on diagram shape feels inelegant. In a static
version of sketched C-sets, this logic would be performed once at compile time.
Even in a dynamic version like this one, we could gain some efficiency by
caching these inferences.
"""
function limit_op(X::SketchedACSet, op::Int, args::AbstractVector)
  args = SVector{length(args)}(args) # Dispatch on binary case where possible.
  in_edges = in_edge(X.sketch, op_inputs(X.sketch, op))
  if isempty(in_edges)
    return terminal(FinSet{Int})
  elseif all(e -> is_reflexive(X.sketch, e), in_edges)
    return product(map(dom, args))
  end

  one_src = allequal(src(X.sketch, in_edges))
  one_tgt = allequal(tgt(X.sketch, in_edges))
  if one_src && one_tgt
    return equalizer(args)
  elseif one_tgt
    # Use hash join to take advantage of already indexed morphisms.
    return pullback(args, alg=HashJoin())
  else
    error("General limits not yet supported in sketched C-sets")
  end
end
is_reflexive(g, e::Int) = !isempty(incident(g, e, :refl))

""" Total function associated with object or morphism in C-set.

Discards any null/undefined values that may be present.
"""
total_function(X::AbstractACSet, args...) =
  total_function(FinFunction(X, args...))

function total_function(f::FinSets.FinFunction)
  # Only throw away original function, including possibly its index, if needed.
  f_vec = collect(f)
  any(==(0), f_vec) ? FinFunction(filter(!=(0), f_vec), codom(f)) : f
end

total_function(f::Sets.SetFunctionIdentity) = f

end

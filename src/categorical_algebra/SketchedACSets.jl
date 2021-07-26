module SketchedACSets
export SketchedACSet

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

# Sketched C-sets
#################

struct SketchedACSet{ACS<:AbstractACSet}
  sketch::Sketch
  acset::ACS
end

# Accessors just delegate to the underlying acset.
@inline nparts(X::SketchedACSet, args...) = nparts(X.acset, args...)
@inline parts(X::SketchedACSet, args...) = parts(X.acset, args...)
@inline subpart(X::SketchedACSet, args...) = subpart(X.acset, args...)
@inline incident(X::SketchedACSet, args...) = incident(X.acset, args...)
@inline has_part(X::SketchedACSet, args...) = has_part(X.acset, args...)
@inline has_subpart(X::SketchedACSet, args...) = has_subpart(X.acset, args...)
@inline Base.getindex(X::SketchedACSet, args...) = getindex(X.acset, args...)

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
  parts = add_parts!(X.acset, ob, n)
  propagate_updates!(X, parts, ob)
  parts
end

set_subparts!(X::SketchedACSet, part; kw...) = for pair in kw
  set_subpart!(X, part, pair...) end
set_subparts!(X::SketchedACSet, part, subparts) = for pair in pairs(subparts)
  set_subpart!(X, part, pair...) end

function set_subpart!(X::SketchedACSet, part, hom::Symbol, subpart)
  isempty(incident(X.sketch, hom_edge(X.sketch, hom), :out_edge)) ||
    error("$hom is a derived morphism; it cannot be directly mutated")
  all(subpart(X.acset, part, hom) .== 0) ||
    error("$hom already defined at element(s) in $part; it cannot be mutated")
  _set_subpart!(X, part, hom, subpart)
end

""" Set subparts in underlying acset, then propagate updates.

Assumes that the subparts have not been previously set.
"""
function _set_subpart!(X::SketchedACSet, part, hom::Symbol, subpart)
  set_subpart!(X.acset, part, hom, subpart)
  propagate_updates!(X, part, hom)
end

function propagate_updates!(X::SketchedACSet, parts, hom::Symbol)
  !isempty(parts) || return
  for input in incident(X.sketch, hom_edge(X.sketch, hom), :in_edge)
    limit_op!(X, X.sketch[input, :op_in], update=input, parts=parts)
  end
end

function limit_op!(X::SketchedACSet, op::Int; update=nothing, parts=nothing)
  args = map(op_inputs(X.sketch, op)) do input
    e = in_edge(X.sketch, input)
    f = FinFunction(X.acset, hom(X.sketch, e))
    input == update ? compose(FinFunction(parts, dom(f)), f) : f
  end

  lim = limit_op(X, op, args)

  v = out_vertex(X.sketch, op)
  parts = _add_parts(X, ob(X.sketch, v), length(ob(lim)))
  for (output, leg) in zip(op_outputs(X.sketch, op), legs(lim))
    e = out_edge(X.sketch, output)
    _set_subpart!(X, parts, hom(X.sketch, e), collect(leg))
  end
end

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

end

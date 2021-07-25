module SketchedCSets

using ...Present, ...Theories, ...Graphs, ..CSets
using ...Syntax: GATExpr
using ...Graphs.BasicGraphs: TheoryReflexiveGraph

# Sketches
##########

@present TheorySketchGraph <: TheoryReflexiveGraph begin
  Name::Data
  ob::Attr(V,Name)
  hom::Attr(E,Name)
end

@present TheorySketch <: TheorySketchGraph begin
  Op::Ob
  out_vert::Hom(Op,V)

  (In, Out)::Ob
  op_in::Hom(In,Op)
  op_out::Hom(Out,Op)
  in_edge::Hom(In,E)
  out_edge::Hom(Out,E)
end

const Sketch = ACSetType(TheorySketch,
  # FIXME: `out_vert` and `out_edge` should be unique-indexed.
  index=[:src, :tgt, :out_vert, :op_in, :op_out, :in_edge, :out_edge],
  unique_index=[:ob, :hom])

function Sketch(pres::Presentation{Schema,Name}) where Name
  sketch = Sketch{Name}()
  add_graph_elements!(sketch, pres)
  sketch
end

function Sketch(pres::Presentation{FinProductSchema,Name}) where Name
  sketch = Sketch{Name}()
  add_graph_elements!(sketch, pres)
  add_product_ops!(sketch, pres)
  sketch
end

function Sketch(pres::Presentation{FinLimitSchema,Name}) where Name
  sketch = Sketch{Name}()
  add_graph_elements!(sketch, pres)
  add_limit_ops!(sketch, pres)
  sketch
end

function add_graph_elements!(sketch::Sketch, pres::Presentation)
  # Add objects and identity morphisms.
  obs = generators(pres, :Ob)
  vs = add_parts!(sketch, :V, length(obs), ob=map(first, obs))
  es = add_parts!(sketch, :E, length(obs), src=vs, tgt=vs, hom=sketch[vs,:ob])
  set_subpart!(sketch, vs, :refl, es)

  # Add morphism generators.
  homs = generators(pres, :Hom)
  srcs = incident(sketch, map(first∘dom, homs), :ob)
  tgts = incident(sketch, map(first∘codom, homs), :ob)
  add_parts!(sketch, :E, length(homs), src=srcs, tgt=tgts, hom=map(first, homs))
end

function add_op!(sketch::Sketch, out, inputs, outputs)
  op = add_part!(sketch, :Op, out_vert=incident(sketch, coerce_arg(out), :ob))
  add_parts!(sketch, :In, length(inputs), op_in=op,
             in_edge=incident(sketch, map(coerce_arg, inputs), :hom))
  add_parts!(sketch, :Out, length(outputs), op_out=op,
             out_edge=incident(sketch, map(coerce_arg, outputs), :hom))
  op
end
coerce_arg(x::GATExpr) = first(x)
coerce_arg(x) = x

function add_product_ops!(sketch::Sketch, pres::Presentation)
  for term in generators(pres, :Terminal)
    add_op!(sketch, ob(term), [], [])
  end
  for prod in generators(pres, :Product)
    π1, π2 = proj1(prod), proj2(prod)
    add_op!(sketch, ob(prod), [codom(π1), codom(π2)], [π1, π2])
  end
end

function add_limit_ops!(sketch::Sketch, pres::Presentation)
  add_product_ops!(sketch, pres)
  for eq in generators(pres, :Equalizer)
    add_op!(sketch, ob(eq), [left(eq), right(eq)], [incl(eq)])
  end
  for pb in generators(pres, :Pullback)
    add_op!(sketch, ob(pb), [left(pb), right(pb)], [proj1(pb), proj2(pb)])
  end
end

end

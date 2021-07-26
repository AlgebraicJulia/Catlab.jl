module TestSketchedACSets
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.CategoricalAlgebra.SketchedACSets: Sketch, op_inputs, op_outputs,
  out_vertex, in_edge, out_edge

# Sketches
##########

function op_signature(sketch::Sketch, op::Int)
  (ob(sketch, out_vertex(sketch, op)),
   hom(sketch, in_edge(sketch, op_inputs(sketch, op))),
   hom(sketch, out_edge(sketch, op_outputs(sketch, op))))
end

# Trivial sketch.
sketch = Sketch(TheoryGraph)
@test (nparts(sketch, :V), nparts(sketch, :E)) == (2, 4)
@test ob(sketch) == [:V,:E]
@test hom(sketch) == [:V,:E,:src,:tgt]
@test nparts(sketch, :Op) == 0

# Finite product sketch.
@present SigMonoid(FreeFinProductSchema) begin
  El::Ob

  El²::Ob
  (fst, snd, times)::Hom(El², El)
  ::Product(El², fst, snd)

  I::Ob
  unit::Hom(I, El)
  ::Terminal(I)
end

sketch = Sketch(SigMonoid)
@test ob(sketch) == [:El, :El², :I]
@test hom(sketch) == [:El, :El², :I, :fst, :snd, :times, :unit]
@test nparts(sketch, :Op) == 2
@test op_signature(sketch, 1) == (:I, [], [])
@test op_signature(sketch, 2) == (:El², [:El,:El], [:fst,:snd])

# Finite limit sketch.
@present SchemaPolyHom(FreeFinLimitSchema) begin
  (B, B′, E, E′)::Ob
  p::Hom(E, B)
  p′::Hom(E′, B′)

  f::Hom(B, B′)

  F::Ob
  πB::Hom(F, B)
  πE′::Hom(F, E′)
  ::Pullback(F, πB, πE′, f, p′)

  f♯::Hom(F, E)
  compose(f♯, p) == πB
end

sketch = Sketch(SchemaPolyHom)
@test nparts(sketch, :Op) == 1
@test op_signature(sketch, 1) == (:F, [:f,:p′], [:πB,:πE′])

end

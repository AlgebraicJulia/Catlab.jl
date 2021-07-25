module TestSketchedCSets
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.CategoricalAlgebra.SketchedCSets: Sketch

# Sketches
##########

# Trivial sketch.
sketch = Sketch(TheoryGraph)
@test (nparts(sketch, :V), nparts(sketch, :E)) == (2, 4)
@test sketch[:ob] == [:V,:E]
@test sketch[:hom] == [:V,:E,:src,:tgt]
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
@test sketch[:ob] == [:El, :El², :I]
@test sketch[:hom] == [:El, :El², :I, :fst, :snd, :times, :unit]
@test nparts(sketch, :Op) == 2
@test sketch[:out_vert] == [3, 2]

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
@test sketch[1,:out_vert] == 5

end

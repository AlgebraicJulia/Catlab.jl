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

# Finite product sketch
#----------------------

@present SigMonoid(FreeFinProductSchema) begin
  El::Ob

  El²::Ob
  (π₁, π₂, μ)::Hom(El², El)
  ::Product(El², π₁, π₂)

  I::Ob
  η::Hom(I, El)
  ::Terminal(I)
end

sketch = Sketch(SigMonoid)
@test ob(sketch) == [:El, :El², :I]
@test hom(sketch) == [:El, :El², :I, :π₁, :π₂, :μ, :η]
@test nparts(sketch, :Op) == 2
@test op_signature(sketch, 1) == (:I, [], [])
@test op_signature(sketch, 2) == (:El², [:El,:El], [:π₁,:π₂])

# Finite limit sketch
#--------------------

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

# Sketched C-sets
#################

# Finite product sketch
#----------------------

const MonoidData = ACSetType(SigMonoid)

M = SketchedACSet(SigMonoid, MonoidData())
@test (nparts(M, :El), nparts(M, :El²), nparts(M, :I)) == (0,0,1)
@test add_part!(M, :El) == 1
@test (nparts(M, :El), nparts(M, :El²)) == (1,1)
M[1,:η] = 1
M[1,:μ] = 1
@test (M[1,:η], M[1,:μ]) == (1, 1)

@test add_parts!(M, :El, 2) == 2:3
@test (nparts(M, :El), nparts(M, :El²)) == (3,9)
@test M[1,:μ] == 1
@test M[:π₁] == [1,2,3, 1,2,3, 1,2,3]
@test M[:π₂] == [1,1,1, 2,2,2, 3,3,3]

# Finite limit sketch
#--------------------

const PolyHomData = ACSetType(SchemaPolyHom, index=[:p, :p′])

ϕ = SketchedACSet(SchemaPolyHom, PolyHomData())
add_parts!(ϕ, :B, 2)
add_parts!(ϕ, :E, 5, p=[1,1,1,2,2])
@test (nparts(ϕ, :B), nparts(ϕ, :E)) == (2,5)
@test ϕ[:p] == [1,1,1,2,2]

add_parts!(ϕ, :B′, 3)
add_parts!(ϕ, :E′, 6, p′=[1,2,2,3,3,3])
@test nparts(ϕ, :F) == 0
ϕ[1:2,:f] = [3,2]
@test ϕ[:f] == [3,2]
@test nparts(ϕ, :F) == 5
@test sort(collect(zip(ϕ[:πB], ϕ[:πE′]))) == [(1,4),(1,5),(1,6),(2,2),(2,3)]
ϕ[1:5,:f♯] = [3,2,1,4,5]
@test ϕ[:f♯] == [3,2,1,4,5]
@test ϕ[[:f♯,:p]] == ϕ[:πB]

add_part!(ϕ, :E′, p′=2) # Add a direction to second position in p′.
@test sort(collect(zip(ϕ[:πB], ϕ[:πE′]))) ==
  [(1,4),(1,5),(1,6),(2,2),(2,3),(2,7)]
@test ϕ[:f♯] == [3,2,1,4,5,0]

end

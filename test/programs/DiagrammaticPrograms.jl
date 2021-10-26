module TestDiagrammaticPrograms
using Test

using Catlab.CategoricalAlgebra, Catlab.Programs.DiagrammaticPrograms
using Catlab.Programs.DiagrammaticPrograms: NamedGraph, MaybeNamedGraph
using Catlab.Graphs.BasicGraphs: TheoryGraph

# Graphs
########

para_parsed = @graph begin
  s
  t
  s → t
  s → t
end
para = @acset MaybeNamedGraph{Symbol} begin
  V = 2
  E = 2
  src = [1,1]
  tgt = [2,2]
  vname = [:s, :t]
  ename = [nothing, nothing]
end
@test para_parsed == para

para_parsed = @graph NamedGraph{Symbol} begin
  x, y
  (f, g): x → y
end
para = @acset NamedGraph{Symbol} begin
  V = 2
  E = 2
  src = [1,1]
  tgt = [2,2]
  vname = [:x, :y]
  ename = [:f, :g]
end
@test para_parsed == para

tri_parsed = @graph NamedGraph{Symbol} begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
tri = @acset NamedGraph{Symbol} begin
  V = 3
  E = 3
  src = [1,2,1]
  tgt = [2,3,3]
  vname = [:v0, :v1, :v2]
  ename = [:fst, :snd, :comp]
end
@test tri_parsed == tri

# Categories
############

Δ¹_parsed = @category begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
Δ¹_graph = @acset NamedGraph{Symbol} begin
  V = 2
  E = 3
  src = [1,1,2]
  tgt = [2,2,1]
  vname = [:V, :E]
  ename = [:δ₀, :δ₁, :σ₀]
end
Δ¹ = FinCat(Δ¹_graph, [ [1,3] => empty(Path, Δ¹_graph, 1),
                        [2,3] => empty(Path, Δ¹_graph, 1) ])
@test Δ¹_parsed == Δ¹

# Diagrams
##########

C = FinCat(TheoryGraph)
F_parsed = @diagram C begin
  v::V
  (e1, e2)::E
  t::tgt : e1 → v
  s::src : e2 → v
end
J = FinCat(@acset NamedGraph{Symbol} begin
  V = 3
  E = 2
  src = [2,3]
  tgt = [1,1]
  vname = [:v, :e1, :e2]
  ename = [:t, :s]
end)
@test dom(F_parsed) == J
F = FinFunctor([:V,:E,:E], [:tgt, :src], J, C)
@test F_parsed == F

F_parsed = @diagram C begin
  v => V
  (e1, e2) => E
  t: e1 → v => tgt
  s: e2 → v => src
end
@test F_parsed == F

end
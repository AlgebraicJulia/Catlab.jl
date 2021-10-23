module TestDiagrammaticPrograms
using Test

using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Programs.DiagrammaticPrograms
using Catlab.Programs.DiagrammaticPrograms: NamedGraph, MaybeNamedGraph
using Catlab.Graphs.BasicGraphs: TheoryGraph

@present TheoryDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

# Graphs
########

g = @graph begin
  s
  t
  s → t
  s → t
end
@test g == parallel_arrows(MaybeNamedGraph{Symbol}, 2,
                           V=(vname=[:s,:t],), E=(ename=[nothing,nothing],))

g = @graph NamedGraph{Symbol} begin
  x, y
  (f, g): x → y
end
@test g == parallel_arrows(NamedGraph{Symbol}, 2,
                           V=(vname=[:x,:y],), E=(ename=[:f,:g],))

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
  (t: e1 → v)::tgt
  (s: e2 → v)::src
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

F_parsed = @diagram TheoryGraph begin
  v => V
  (e1, e2) => E
  t: e1 → v => tgt
  s: e2 → v => src
end
@test F_parsed == F

F = @diagram TheoryDDS begin
  x::X
  (f: x → x)::(Φ⋅Φ)
end
@test only(collect_ob(F)) == TheoryDDS[:X]
@test only(collect_hom(F)) == compose(TheoryDDS[:Φ], TheoryDDS[:Φ])

# Migrations
############

# Pullback migration
#-------------------

F = @migration TheoryGraph begin
  E => E
  V => V
  (src: E → V) => tgt
  (tgt: E → V) => src
end
J = FinCat(parallel_arrows(NamedGraph{Symbol}, 2,
                           V=(vname=[:E,:V],), E=(ename=[:src,:tgt],)))
@test F == FinDomFunctor([:E,:V], [:tgt,:src], J, FinCat(TheoryGraph))

# Conjunctive migration
#----------------------

F = @migration TheoryGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    (t: e₁ → v)::tgt
    (s: e₂ → v)::src
  end
  (src: E → V) => e₁ ⋅ src
  (tgt: E → V) => e₂ ⋅ tgt
end
F_E = diagram(ob_map(F, 2))
@test nameof.(collect_ob(F_E)) == [:V, :E, :E]
@test nameof.(collect_hom(F_E)) == [:tgt, :src]
F_tgt = hom_map(F, 2)
@test ob_map(F_tgt, 1) == (3, TheoryGraph[:tgt])

end

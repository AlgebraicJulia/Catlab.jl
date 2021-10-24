module TestDiagrammaticPrograms
using Test

using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Programs.DiagrammaticPrograms
using Catlab.Programs.DiagrammaticPrograms: NamedGraph, MaybeNamedGraph
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.WiringDiagrams.CPortGraphs: ThCPortGraph

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

Δ¹_parsed = @fincat begin
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

# Functors
##########

F = @finfunctor TheoryGraph ThCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
@test F == FinFunctor(Dict(:V => :Box, :E => :Wire),
                      Dict(:src => [:src, :box], :tgt => [:tgt, :box]),
                      TheoryGraph, ThCPortGraph)

# Incomplete definition.
@test_throws ErrorException @finfunctor(TheoryGraph, ThCPortGraph, begin
  V => Box
  src => src ⨟ box
  tgt => tgt ⨟ box
end)

# Failure of functorality.
@test_throws ErrorException (@finfunctor TheoryGraph ThCPortGraph begin
  V => Box
  E => Wire
  src => src
  tgt => tgt
end)

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

# Reverse edge directions.
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

# Graph with edges that are paths of length 2.
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

# Reflexive graph from graph.
F = @migration TheoryGraph begin
  V => @join begin
    v::V
    ℓ::E
    (s: ℓ → v)::src
    (t: ℓ → v)::tgt
  end
  E => @join begin
    (v₁, v₂)::V
    (ℓ₁, ℓ₂, e)::E
    (s₁: ℓ₁ → v₁)::src
    (t₁: ℓ₁ → v₁)::tgt
    (s₂: ℓ₂ → v₂)::src
    (t₂: ℓ₂ → v₂)::tgt
    (s: e → v₁)::src
    (t: e → v₂)::tgt
  end
  (refl: V → E) => begin
    (v₁, v₂) => v
    (ℓ₁, ℓ₂, e) => ℓ
    (s₁, s₂, s) => s
    (t₁, t₂, t) => t
  end
  (src: E → V) => begin
    v => v₁; ℓ => ℓ₁; s => s₁; t => t₁
  end
  (tgt: E → V) => begin
    v => v₂; ℓ => ℓ₂; s => s₂; t => t₂
  end
end
F_tgt = hom_map(F, 3)
@test ob_map(F_tgt, 1) == (2, id(TheoryGraph[:V]))
@test hom_map(F_tgt, 2) |> edges |> only == 4

end

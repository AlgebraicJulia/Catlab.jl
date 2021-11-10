module TestDiagrammaticPrograms
using Test

using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Programs.DiagrammaticPrograms
using Catlab.Programs.DiagrammaticPrograms: NamedGraph, MaybeNamedGraph
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheoryReflexiveGraph
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

# Underlying graph of circular port graph.
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

# Graph with reversed edges.
F = @migration TheoryGraph TheoryGraph begin
  V => V
  E => E
  src => tgt
  tgt => src
end
@test F == FinFunctor(Dict(:V => :V, :E => :E),
                      Dict(:src => :tgt, :tgt => :src),
                      TheoryGraph, TheoryGraph)

# Variant where target schema is not given.
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
F = @migration TheoryGraph TheoryGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    (t: e₁ → v)::tgt
    (s: e₂ → v)::src
  end
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
end
F_E = diagram(ob_map(F, :E))
@test nameof.(collect_ob(F_E)) == [:V, :E, :E]
@test nameof.(collect_hom(F_E)) == [:tgt, :src]
F_tgt = hom_map(F, :tgt)
@test ob_map(F_tgt, 1) == (3, TheoryGraph[:tgt])

# Cartesian product of graph with itself.
F = @migration TheoryGraph TheoryGraph begin
  V => @product (v₁::V; v₂::V)
  E => @product (e₁::E; e₂::E)
  src => (v₁ => e₁⋅src; v₂ => e₂⋅src)
  tgt => (v₁ => e₁⋅tgt; v₂ => e₂⋅tgt)
end
F_V = diagram(ob_map(F, :V))
@test collect_ob(F_V) == fill(TheoryGraph[:V], 2)
F_src = hom_map(F, :src)
@test ob_map(F_src, 2) == (2, TheoryGraph[:src])

# Reflexive graph from graph.
F = @migration TheoryReflexiveGraph TheoryGraph begin
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
  refl => begin
    (v₁, v₂) => v
    (ℓ₁, ℓ₂, e) => ℓ
    (s₁, s₂, s) => s
    (t₁, t₂, t) => t
  end
  src => begin
    v => v₁; ℓ => ℓ₁; s => s₁; t => t₁
  end
  tgt => begin
    v => v₂; ℓ => ℓ₂; s => s₂; t => t₂
  end
end
F_tgt = hom_map(F, :tgt)
@test ob_map(F_tgt, 1) == (2, id(TheoryGraph[:V]))
@test hom_map(F_tgt, 2) |> edges |> only == 4

# Free/initial port graph on a graph.
# This is the left adjoint to the underlying graph functor.
F = @migration TheoryGraph begin
  Box => V
  Wire => E
  InPort => @join begin
    v::V
    e::E
    (t: e → v)::tgt
  end
  OutPort => @join begin
    v::V
    e::E
    (s: e → v)::src
  end
  (in_port_box: InPort → Box) => v
  (out_port_box: OutPort → Box) => v
  (src: Wire → OutPort) => begin
    v => src
  end
  (tgt: Wire → InPort) => begin
    v => tgt
  end
end
F_src = hom_map(F, 3)
@test ob_map(F_src, 1) == (1, TheoryGraph[:src])
@test ob_map(F_src, 2) == (1, id(TheoryGraph[:E]))
@test hom_map(F_src, 1) == id(shape(codom(F_src)), 1)

# Agglomerative migration
#------------------------

# Coproduct of graph with itself.
F = @migration TheoryGraph TheoryGraph begin
  V => @cases (v₁::V; v₂::V)
  E => @cases (e₁::E; e₂::E)
  src => (e₁⋅src => v₁; e₂⋅src => v₂)
  tgt => (e₁⋅tgt => v₁; e₂⋅tgt => v₂)
end
F_V = diagram(ob_map(F, :V))
@test collect_ob(F_V) == fill(TheoryGraph[:V], 2)
F_src = hom_map(F, :src)
@test ob_map(F_src, 2) == (2, TheoryGraph[:src])

# Free reflexive graph on a graph.
F = @migration TheoryReflexiveGraph TheoryGraph begin
  V => V
  E => @cases (e::E; v::V)
  src => (e⋅src; v)
  tgt => (e⋅tgt; v)
  refl => v
end
F_tgt = hom_map(F, :tgt)
@test ob_map(F_tgt, 1) == (1, TheoryGraph[:tgt])
@test ob_map(F_tgt, 2) == (1, id(TheoryGraph[:V]))

# Same query but with syntactic variations.
F′ = @migration TheoryReflexiveGraph TheoryGraph begin
  V => V
  E => @coproduct begin
    e::E
    v::V
  end
  src => begin
    e => src
  end
  tgt => begin
    e => tgt
  end
  refl => v
end
@test F′ == F

end

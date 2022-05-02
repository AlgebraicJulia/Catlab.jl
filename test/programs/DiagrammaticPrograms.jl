module TestDiagrammaticPrograms
using Test

using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Programs.DiagrammaticPrograms
using Catlab.Programs.DiagrammaticPrograms: NamedGraph
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheoryReflexiveGraph
using Catlab.Graphs.BipartiteGraphs: TheoryBipartiteGraph
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
@test g == parallel_arrows(NamedGraph{Symbol,Union{Symbol,Nothing}}, 2,
                           V=(vname=[:s,:t],), E=(ename=[nothing,nothing],))

g = @graph NamedGraph{Symbol,Symbol} begin
  x, y
  (f, g): x → y
end
@test g == parallel_arrows(NamedGraph{Symbol,Symbol}, 2,
                           V=(vname=[:x,:y],), E=(ename=[:f,:g],))

tri_parsed = @graph NamedGraph{Symbol,Symbol} begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
tri = @acset NamedGraph{Symbol,Symbol} begin
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
Δ¹_graph = @acset NamedGraph{Symbol,Symbol} begin
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
@test_throws ErrorException begin
  @finfunctor TheoryGraph ThCPortGraph begin
    V => Box
    src => src ⨟ box
    tgt => tgt ⨟ box
  end
end

# Failure of functorality.
@test_throws ErrorException begin
  @finfunctor TheoryGraph ThCPortGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
  end
end

# Extra definitions.
@test_throws ErrorException begin
  @finfunctor TheoryGraph TheoryReflexiveGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
    refl => refl
  end
end

# GAT expressions.
F = @finfunctor TheoryDDS TheoryDDS begin
  X => X; Φ => id(X)
end
F′ = @finfunctor TheoryDDS TheoryDDS begin
  X => X; Φ => id{X}
end
@test F == F′

# Diagrams
##########

C = FinCat(TheoryGraph)
F_parsed = @diagram C begin
  v::V
  (e1, e2)::E
  (t: e1 → v)::tgt
  (s: e2 → v)::src
end
J = FinCat(@acset NamedGraph{Symbol,Union{Symbol,Nothing}} begin
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

F_parsed = @diagram TheoryGraph begin
  v::V
  (e1, e2)::E
  (e1 → v)::tgt
  (e2 → v)::src
end
J_parsed = dom(F_parsed)
@test src(graph(J_parsed)) == src(graph(J))
@test tgt(graph(J_parsed)) == tgt(graph(J))

F_parsed′ = @free_diagram TheoryGraph begin
  v::V
  (e1, e2)::E
  tgt(e1) == v
  v == src(e2)
end
@test F_parsed′ == F_parsed

F = @free_diagram TheoryGraph begin
  (e1, e2)::E
  tgt(e1) == src(e2)
end
@test is_functorial(F)
@test collect_ob(F) == [TheoryGraph[:E], TheoryGraph[:E], TheoryGraph[:V]]
@test collect_hom(F) == [TheoryGraph[:tgt], TheoryGraph[:src]]

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
@test F isa DataMigrations.DeltaSchemaMigration
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
J = FinCat(parallel_arrows(NamedGraph{Symbol,Union{Symbol,Nothing}}, 2,
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
    (e₁ → v)::tgt
    (e₂ → v)::src
  end
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
end
@test F isa DataMigrations.ConjSchemaMigration
F_E = diagram(ob_map(F, :E))
@test nameof.(collect_ob(F_E)) == [:V, :E, :E]
@test nameof.(collect_hom(F_E)) == [:tgt, :src]
F_tgt = hom_map(F, :tgt)
@test collect_ob(F_tgt) == [(3, TheoryGraph[:tgt])]

# Syntactic variant of above.
F′ = @migration TheoryGraph TheoryGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    tgt(e₁) == v
    src(e₂) == v
  end
  src => src(e₁)
  tgt => tgt(e₂)
end
@test F′ == F

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
@test collect_ob(F_src) == [(1, TheoryGraph[:src]), (2, TheoryGraph[:src])]

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
@test ob_map(F_tgt, :v) == (2, id(TheoryGraph[:V]))
@test hom_map(F_tgt, :t) |> edges |> only == 4

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
F_src = hom_map(F, :src)
@test collect_ob(F_src) == [(1, TheoryGraph[:src]), (1, id(TheoryGraph[:E]))]
@test collect_hom(F_src) == [id(shape(codom(F_src)), 1)]

# Gluing migration
#-----------------

# Coproduct of graph with itself.
F = @migration TheoryGraph TheoryGraph begin
  V => @cases (v₁::V; v₂::V)
  E => @cases (e₁::E; e₂::E)
  src => begin
    e₁ => v₁ ∘ src
    e₂ => v₂ ∘ src
  end
  tgt => begin
    e₁ => v₁ ∘ tgt
    e₂ => v₂ ∘ tgt
  end
end
@test F isa DataMigrations.GlueSchemaMigration
F_V = diagram(ob_map(F, :V))
@test collect_ob(F_V) == fill(TheoryGraph[:V], 2)
F_src = hom_map(F, :src)
@test collect_ob(F_src) == [(1, TheoryGraph[:src]), (2, TheoryGraph[:src])]

# Free reflexive graph on a graph.
F = @migration TheoryReflexiveGraph TheoryGraph begin
  V => V
  E => @cases (e::E; v::V)
  src => (e => src)
  tgt => (e => tgt)
  refl => v
end
F_tgt = hom_map(F, :tgt)
@test collect_ob(F_tgt) == [(1, TheoryGraph[:tgt]), (1, id(TheoryGraph[:V]))]

# Vertices in a graph and their connected components.
F = @migration TheoryGraph begin
  V => V
  Component => @glue begin
    e::E; v::V
    (e → v)::src
    (e → v)::tgt
  end
  (component: V → Component) => v
end
F_C = diagram(ob_map(F, :Component))
@test nameof.(collect_ob(F_C)) == [:E, :V]
@test nameof.(collect_hom(F_C)) == [:src, :tgt]

# Gluc migration
#---------------

# Graph with edges that are paths of length <= 2.
F = @migration TheoryGraph TheoryGraph begin
  V => V
  E => @cases begin
    v => V
    e => E
    path => @join begin
      v::V
      (e₁, e₂)::E
      (e₁ → v)::tgt
      (e₂ → v)::src
    end
  end
  src => begin
    e => src
    path => e₁⋅src
  end
  tgt => begin
    e => tgt
    path => e₂⋅tgt
  end
end
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test F isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,1,1]
F_src_v, F_src_e, F_src_path = components(diagram_map(F_src))
@test collect_ob(F_src_v) == [(1, id(TheoryGraph[:V]))]
@test collect_ob(F_src_e) == [(1, TheoryGraph[:src])]
@test collect_ob(F_src_path) == [(2, TheoryGraph[:src])]

# Graph with edges that are minimal paths b/w like vertices in bipartite graph.
F = @migration TheoryGraph TheoryBipartiteGraph begin
  V => @cases (v₁::V₁; v₂::V₂)
  E => @cases begin
    e₁ => @join begin
      v₂::V₂; e₁₂::E₁₂; e₂₁::E₂₁
      (e₁₂ → v₂)::tgt₂
      (e₂₁ → v₂)::src₂
    end
    e₂ => @join begin
      v₁::V₁; e₂₁::E₂₁; e₁₂::E₁₂
      (e₂₁ → v₁)::tgt₁
      (e₁₂ → v₁)::src₁
    end
  end
  src => begin
    e₁ => v₁ ∘ (e₁₂ ⋅ src₁)
    e₂ => v₂ ∘ (e₂₁ ⋅ src₂)
  end
  tgt => begin
    e₁ => v₁ ∘ (e₂₁ ⋅ tgt₁)
    e₂ => v₂ ∘ (e₁₂ ⋅ tgt₂)
  end
end
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test F isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,2]
F_src1, F_src2 = components(diagram_map(F_src))
@test collect_ob(F_src1) == [(2, TheoryBipartiteGraph[:src₁])]
@test collect_ob(F_src2) == [(2, TheoryBipartiteGraph[:src₂])]

# Box product of reflexive graph with itself.
F = @migration TheoryReflexiveGraph TheoryReflexiveGraph begin
  V => @product (v₁::V; v₂::V)
  E => @glue begin
    vv => @product (v₁::V; v₂::V)
    ev => @product (e₁::E; v₂::V)
    ve => @product (v₁::V; e₂::E)
    (refl₁: vv → ev) => (e₁ => v₁⋅refl; v₂ => v₂)
    (refl₂: vv → ve) => (v₁ => v₁; e₂ => v₂⋅refl)
  end
  src => begin
    ev => (v₁ => e₁⋅src; v₂ => v₂)
    ve => (v₁ => v₁; v₂ => e₂⋅src)
  end
  tgt => begin
    ev => (v₁ => e₁⋅tgt; v₂ => v₂)
    ve => (v₁ => v₁; v₂ => e₂⋅tgt)
  end
  refl => vv
end
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test F isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,1,1]
F_src_vv, F_src_ev, F_src_ve = components(diagram_map(F_src))
@test collect_ob(F_src_ev) == [(1, TheoryReflexiveGraph[:src]),
                               (2, id(TheoryReflexiveGraph[:V]))]

end

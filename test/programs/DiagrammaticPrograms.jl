module TestDiagrammaticPrograms
using Test

using Catlab.GATs, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Theories: FreePtCategory
using Catlab.Programs.DiagrammaticPrograms, Catlab.CategoricalAlgebra.DataMigrations
using Catlab.Programs.DiagrammaticPrograms: NamedGraph
using Catlab.Programs.DiagrammaticPrograms: get_keyword_arg_val, destructure_unary_call
using Catlab.WiringDiagrams.CPortGraphs

module enums
  using MLStyle
  @data BinaryMarks begin 
    X
    O
    Blank
  end
  @data TwoStates begin
    start
    stop
  end
end

@present SchSet(FreeSchema) begin
  X::Ob
end
@present SchDDS <: SchSet begin
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
@test subpart(g,:vname) == [:s,:t]

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
F = @finfunctor SchGraph SchCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
@test F == FinFunctor(Dict(:V => :Box, :E => :Wire),
                      Dict(:src => [:src, :box], :tgt => [:tgt, :box]),
                      SchGraph, SchCPortGraph)

# Incomplete definitions.
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
  end
end
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
    src => src ⨟ box
    tgt => tgt ⨟ box
  end
end

# Failure of functorality.
@test_throws ErrorException begin
  @finfunctor SchGraph SchCPortGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
  end
end

# Extra definitions.
@test_throws ErrorException begin
  @finfunctor SchGraph SchReflexiveGraph begin
    V => Box
    E => Wire
    src => src
    tgt => tgt
    refl => refl
  end
end

# GAT expressions.
F = @finfunctor SchDDS SchDDS begin
  X => X; Φ => id(X)
end
F′ = @finfunctor SchDDS SchDDS begin
  X => X; Φ => id{X}
end
@test F == F′

# Diagrams
##########

C = FinCat(SchGraph)
d = @diagram C begin
  v::V
  (e1, e2)::E
  (t: e1 → v)::tgt
  (s: e2 → v)::src
end
J = FinCat(@present P(FreeCategory) begin
  (v,e1,e2)::Ob
  t::Hom(e1,v)
  s::Hom(e2,v)
end)
F_parsed = diagram(d)
@test dom(F_parsed) == J
F = FinFunctor(Dict(:v=>:V,:e1=>:E,:e2=>:E), 
              Dict(:t=>:tgt,:s=>:src), J, C)
@test F_parsed == F

d = @diagram SchGraph begin
  v => V
  (e1, e2) => E
  t: e1 → v => tgt
  s: e2 → v => src
end
@test diagram(d) == F

d = @diagram SchGraph begin
  v::V
  (e1, e2)::E
  (e1 → v)::tgt
  (e2 → v)::src
end
F_parsed = diagram(d)
J_parsed = dom(F_parsed)
@test src(graph(J_parsed)) == src(graph(J))
@test tgt(graph(J_parsed)) == tgt(graph(J))

d′ = @free_diagram SchGraph begin
  v::V
  (e1, e2)::E
  tgt(e1) == v
  v == src(e2)
end
@test d′ == d

d = @free_diagram SchGraph begin
  (e1, e2)::E
  tgt(e1) == src(e2)
end
@test is_functorial(diagram(d))
@test collect_ob(d) == SchGraph[[:E, :E, :V]]
@test collect_hom(d) == SchGraph[[:tgt, :src]]

d = @diagram SchDDS begin
  x::X
  (f: x → x)::(Φ⋅Φ)
end
@test only(collect_ob(d)) == SchDDS[:X]
@test only(collect_hom(d)) == compose(SchDDS[:Φ], SchDDS[:Φ])

# Migrations
############

# Pullback migration
#-------------------

# Graph with reversed edges.
M = @migration SchGraph SchGraph begin
  V => V
  E => E
  src => tgt
  tgt => src
end
@test M isa DataMigrations.DeltaSchemaMigration
#The functors aren't quite equal because of a trivial
#domain difference, might be worth switching theory for
#total migrations once they're built.
@test functor(M) == FinFunctor(Dict(:V => :V, :E => :E),
                      Dict(:src => :tgt, :tgt => :src),
                      SchGraph, SchGraph)

# Variant where target schema is not given.
M = @migration SchGraph begin
  V => V
  E => E
  (src: E → V) => tgt
  (tgt: E → V) => src
end
J = FinCat(@present P(FreeSchema) begin
           (V,E)::Ob
           (src,tgt)::Hom(E,V)
end)

@test functor(M) == FinDomFunctor(Dict(:E=>:E,:V=>:V), Dict(:tgt=>:src,:src=>:tgt), J, FinCat(SchGraph))

# Conjunctive migration
#----------------------

# Graph with edges that are paths of length 2.
M = @migration SchGraph SchGraph begin
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
#Syntactic variant
@migration SchGraph SchGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    (e₁ → v)::tgt
    (e₂ → v)::src
  end
  src => src∘e₁
  tgt => tgt∘e₁
end
@test M isa DataMigrations.ConjSchemaMigration
F = functor(M)
F_E = diagram(ob_map(F, :E))
@test nameof.(collect_ob(F_E)) == [:V, :E, :E]
@test nameof.(collect_hom(F_E)) == [:tgt, :src]
F_tgt = hom_map(F, :tgt)
@test collect_ob(F_tgt)[1][2] == SchGraph[:tgt]

# Syntactic variant of above.
M′ = @migration SchGraph SchGraph begin
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
@test functor(M′) == F

# "Bouquet graph" on set.
# This is the right adjoint to the underlying edge set functor.
M = @migration SchGraph SchSet begin
  V => @product begin end
  E => X
  src => begin end
  tgt => begin end
end
@test M isa DataMigrations.ConjSchemaMigration
@test isempty(shape(ob_map(functor(M), :V)))

# Syntactic variant of above.
M′ = @migration SchGraph SchSet begin
  V => @unit
  E => X
end
@test M′ isa DataMigrations.ConjSchemaMigration
@test isempty(shape(ob_map(functor(M′), :V)))
# This one is a bit messed up because of dict/vector stuff
@test_skip functor(M′) == functor(M) && M′.params == M.params

# Cartesian product of graph with itself.
M = @migration SchGraph SchGraph begin
  V => @product (v₁::V; v₂::V)
  E => @product (e₁::E; e₂::E)
  src => (v₁ => e₁⋅src; v₂ => e₂⋅src)
  tgt => (v₁ => e₁⋅tgt; v₂ => e₂⋅tgt)
end
F = functor(M)
F_V = diagram(ob_map(F, :V))
@test collect_ob(F_V) == fill(SchGraph[:V], 2)
s = hom_generators(dom(F))[1]
F_src = hom_map(F, :src)
@test F_src.diagram_map.components == Dict(:v₂=>s,:v₁=>s)

# Reflexive graph from graph.
M = @migration SchReflexiveGraph SchGraph begin
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
F = functor(M)
F_tgt = hom_map(F, :tgt)
@test ob_map(F_tgt, :v)[2] == id(SchGraph[:V])

# Free/initial port graph on a graph.
# This is the left adjoint to the underlying graph functor.
# univariate things broken, need to unpoint
M = @migration SchGraph begin
  Box => V
  #still seem to need to make this 
  #fincatpresentations
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
F = functor(M)
F_src = hom_map(F, :src)
@test collect_ob(F_src) == [(1, :v=>SchGraph[:src]),(1,id(SchGraph[:E]))]
@test collect_hom(F_src) == [id(shape(dom(F_src)), 1)]

yGraph = yoneda(Graph)

#won't even build
@migration(SchGraph, begin 
  I => @join begin v::V end 
end)

@test is_isomorphic(
  @acset(Graph, begin E=2;V=3;src=[1,2];tgt=[2,3] end),
  @acset_colim(yGraph, begin (e1,e2)::E; src(e1) == tgt(e2) end)
)

# Gluing migration
#-----------------

# Discrete graph on set.
# This is the left adjoint to the underlying vertex set functor.
M = @migration SchGraph SchSet begin
  V => X
  E => @empty
end
F = functor(M)
@test M isa DataMigrations.GlueSchemaMigration
@test isempty(shape(ob_map(F, :E)))

# Coproduct of graph with itself.
M = @migration SchGraph SchGraph begin
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
@test M isa DataMigrations.GlueSchemaMigration
F = functor(M)
F_V = diagram(ob_map(F, :V))
@test collect_ob(F_V) == fill(SchGraph[:V], 2)
F_src = hom_map(F, :src)
#taaaaahpes
@test [x[2] for x in collect_ob(F_src)] == [:(e₁) =>  SchGraph[:src], :(e₂) => SchGraph[:src]]

# Free reflexive graph on a graph.
#infinite loooooop
M = @migration SchReflexiveGraph SchGraph begin
  V => V
  E => @cases (e::E; v::V)
  src => (e => src)
  tgt => (e => tgt)
  refl => v
end
F = functor(M)
F_tgt = hom_map(F, :tgt)
@test collect_ob(F_tgt) == [(1, SchGraph[:tgt]), (1, id(SchGraph[:V]))]

# Vertices in a graph and their connected components.
#actually broken
M = @migration SchGraph begin
  V => V
  Component => @glue begin
    e::E; v::V
    (e → v)::src
    (e → v)::tgt
  end
  (component: V → Component) => v
end
F = functor(M)
F_C = diagram(ob_map(F, :Component))
@test nameof.(collect_ob(F_C)) == [:E, :V]
@test nameof.(collect_hom(F_C)) == [:src, :tgt]

# Gluc migration
#---------------

# Labeled graph with edges that are paths of length <= 2.
M = @migration SchLabeledGraph SchLabeledGraph begin
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
  Label => Label
  label => label
end
F = functor(M)
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test M isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,1,1]
F_src_v, F_src_e, F_src_path = collect(values(components(diagram_map(F_src))))
#I think this is wrong
@test collect_ob(F_src_v) == [(1, id(SchGraph[:V]))]
@test collect_ob(F_src_e) == [(Ob(FreeCategory,:(e₁)), SchGraph[:src])]
@test collect_ob(F_src_path) == [(2, SchGraph[:src])]

# Graph with edges that are minimal paths b/w like vertices in bipartite graph.
M = @migration SchGraph SchBipartiteGraph begin
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
F = functor(M)
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test M isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,2]
F_src1, F_src2 = components(diagram_map(F_src))
@test collect_ob(F_src1) == [(2, SchBipartiteGraph[:src₁])]
@test collect_ob(F_src2) == [(2, SchBipartiteGraph[:src₂])]

# Box product of reflexive graph with itself.
#broken, problem with `head`
M = @migration SchReflexiveGraph SchReflexiveGraph begin
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
F = functor(M)
@test ob_map(F, :V) isa DataMigrations.GlucQuery
@test M isa DataMigrations.GlucSchemaMigration
F_src = hom_map(F, :src)
@test collect_ob(shape_map(F_src)) == [1,1,1]
F_src_vv, F_src_ev, F_src_ve = components(diagram_map(F_src))
@test collect_ob(F_src_ev) == [(1, SchReflexiveGraph[:src]),
                               (2, id(SchReflexiveGraph[:V]))]

#Little parsing functions
@test get_keyword_arg_val(:(x=3)) == 3
@test_throws ErrorException get_keyword_arg_val(:("not an assignment!"+3))
@test destructure_unary_call(:(f(g(x)))) == (:(f∘g),:x)

# Migrations with code
#
#------------------------------------
#@testset "Migrations with code" begin
  @present SchMechLink <: SchGraph begin
      Pos::AttrType
      Len::AttrType
      pos::Attr(V,Pos)
      len::Attr(E,Len)
  end
  @acset_type MechLink(SchMechLink, index=[:src,:tgt])
  G = @acset MechLink{Vector{Float64},Float64} begin
      V = 3
      E = 2
      src = [1,2]
      tgt = [2,3]
      len = [1.0,1.0]
      pos = [[1.0,1.0,1.0],[2.0,2.0,2.0],[2.0,2.0,1.0]]
  end
  
  #Rotate the whole linkage by a bit
  M = @migration SchMechLink SchMechLink begin
      V => V
      E => E
      Pos => Pos
      Len => Len
      src => src
      tgt => tgt
      pos => begin 
              θ = π/5
              M = [[cos(θ),sin(θ),0] [-sin(θ),cos(θ),0] [0,0,1]]
              x -> M*pos(x)
              end
      len => len
  end
  A = migrate(MechLink,G,M)
  v₃ = subpart(A,1,:pos)
  v₂ = v₃[1:2]
  angle(v,w)=acos( sum(v.*w)/(sqrt(sum(v.^2)*sum(w.^2))) )
  @test angle(v₂,[1,1]) == π/5 && v₃[3] == 1
  #Filter impossible edges out of a mechanical linkage
  M = @migration SchMechLink SchMechLink begin
      V => V
      E => @join begin
              e :: E
              L :: Len
              (l:e→L) :: (x->len(x)^2)
              (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
          end
      Pos => Pos
      Len => Len
      src => src(e)
      tgt => tgt(e)
      pos => pos
      len => len(e)
  end
  B = migrate(MechLink,G,M)
  @test length(parts(B,:E)) == 1
  #variant
  M = @migration SchMechLink begin
      V => V
      E => @join begin
              e :: E
              L :: Len
              (l:e→L) :: (x->len(x)^2)
              (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
          end
      Pos => Pos
      Len => Len
      (src:E→V) => src(e)
      (tgt:E→V) => tgt(e)
      (pos:V→Pos) => pos
      (len:E→Len) => len(e)
  end
  Bb = migrate(G,M)
  @test length(ob_map(Bb,:E)) == 1
  #Filter impossible edges out of a mechanical linkage while rotating
  M = @migration SchMechLink SchMechLink begin
      V => V
      E => @join begin
              e :: E
              L :: Len
              (l:e→L) :: (x->len(x)^2)
              (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
          end
      Pos => Pos
      Len => Len
      src => src(e)
      tgt => tgt(e)
      pos => begin 
              θ = π/5
              M = [[cos(θ),sin(θ),0] [-sin(θ),cos(θ),0] [0,0,1]]
              x -> M*pos(x)
              end
      len => len(e)
  end
  C = migrate(MechLink,G,M)
  @test subpart(C,:,:pos) == subpart(A, :, :pos)
  @test length(parts(C,:E))==1
  #Filter out impossible edges, but then weirdly double all the lengths
  M = @migration SchMechLink begin
      V => V
      E => @join begin
          e :: E
          L :: Len
          (l:e→L) :: (x->len(x)^2)
          (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
      end
      Pos => Pos
      Len => Len
      (src:E→V) => src(e)
      (tgt:E→V) => tgt(e)
      (pos:V→Pos) => pos
      (len:E→Len) => (len(e)|>(x->2x))
  end
  D = migrate(G,M)
  @test hom_map(D,:len)(1) == 2.0
  #Variant
  M = @migration SchMechLink SchMechLink begin
    V => V
    E => @join begin
        e :: E
        L :: Len
        (l:e→L) :: (x->len(x)^2)
        (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
    end
    Pos => Pos
    Len => Len
    src => src(e)
    tgt => tgt(e)
    pos => pos
    len => (len(e)|>(x->2x))
end
  Dd = migrate(MechLink,G,M)
  @test only(subpart(Dd,:len)) == 2.0
  #disjoint union linkage with itself, second copy reflected through origin
  #TODO:colimits and zeroes/presentables
  M = @migration SchMechLink SchMechLink begin
    V => @cases (v₁::V;v₂::V)
    E=> @cases (e₁::E;e₂::E)
    Pos => Pos
    Len => Len
    src => begin
      e₁ => v₁ ∘ src
      e₂ => v₂ ∘ src
    end
    tgt => begin
      e₁ => v₁ ∘ tgt
      e₂ => v₂ ∘ tgt
    end
    pos => begin
      v₁ => pos
      v₂ => (pos|> (x-> -x)) 
    end
    len => (e₁ => len ; e₂ => len)
  end
  #=variant,TODO
  M = @migration SchMechLink SchMechLink begin
    V => @cases (v₁::V;v₂::V)
    E=> @cases (e₁::E;e₂::E)
    Pos => Pos
    Len => Len
    src => begin
      e₁ => v₁ ∘ src
      e₂ => v₂ ∘ src
    end
    tgt => begin
      e₁ => v₁ ∘ tgt
      e₂ => v₂ ∘ tgt
    end
    pos => begin
      v₁ => pos
      v₂ => (x->-pos(x))
    end
    len => (e₁ => len ; e₂ => len)
  end
  =#
  #Filter impossible edges and also make a copy reflected through the
  #origin.
  M = @migration SchMechLink SchMechLink begin
    V => @cases (v₁::V;v₂::V)
    E=> @cases begin 
      e₁ => @join begin
        e :: E
        L :: Len
        (l:e→L) :: (x->len(x)^2)
        (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
    end
      e₂ => @join begin
        e :: E
        L :: Len
        (l:e→L) :: (x->len(x)^2)
        (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
    end
  end
    Pos => Pos
    Len => Len
    src => begin
      e₁ => v₁ ∘ (e⋅src)
      e₂ => v₂ ∘ (e⋅src)
    end
    tgt => begin
      e₁ => v₁ ∘ (e⋅tgt)
      e₂ => v₂ ∘ (e⋅tgt)
    end
    pos => begin
      v₁ => pos
      v₂ => (pos|> (x-> -x)) 
    end
    len => (e₁ => e⋅len ; e₂ => e⋅len)
  end

####Turing machines?!?!
@present SchTuringMachine(FreeSchema) begin
  H :: Ob
  T :: Ob
  States :: AttrType
  Marks :: AttrType
  p :: Hom(H,T)
  l :: Hom(T,T)
  r :: Hom(T,T)
  state :: Attr(H,States)
  marks :: Attr(T,Marks)
end
@acset_type TuringMachine(SchTuringMachine)

T = @acset TuringMachine{enums.TwoStates,enums.BinaryMarks} begin
  H = 1
  T = 128
  p = [1]
  r = [2:128;1] #would be nice to get lambdas here!
  l = [128;1:127]
  state = [enums.start]
  marks = [enums.O;map(x->enums.Blank,1:5);enums.X;map(x->enums.Blank,1:121)]
end
M = @migration SchTuringMachine SchTuringMachine begin
  H => H
  T => T
  States => States 
  Marks => Marks 
  p => begin 
    υ(m,s) = begin
            m == enums.Blank ? r :
            m == enums.O ? r : identity
    end
    x->υ(marks(p(x)),state(x))(p(x))
    end
  state => begin 
    σ(m,s) = s == enums.stop ? enums.stop :
              m == enums.X ? enums.stop :
              enums.start
    x -> σ(marks(p(x)),state(x))  
    end
  r => r
  l => l
  marks => begin 
    μ(m,s) = s == enums.start ? 
            (m == enums.Blank ? enums.O :
              m == enums.O ? enums.O : enums.X) :
              m
    x -> x == p(1) ? μ(marks(x),state(1)) : marks(x)
    end
  end
  run_TM(T,n) = n == 0 ? T : run_TM(migrate(TuringMachine,T,M),n-1)
  @test begin subpart(run_TM(T,10),1:8,:marks) == Union{AttrVar,enums.BinaryMarks}[map(x->enums.O,1:6);enums.X;enums.Blank] end
end
#Aggregation
@present SchTwoThings(FreeSchema) begin
  Th1::Ob
  Th2::Ob
  Property::AttrType
  f::Hom(Th1,Th2)
end
@present SchTwoThings2Prop <: SchTwoThings begin
  prop::Attr(Th2,Property)
end
@acset_type TwoThings2Prop(SchTwoThings2Prop)
@present SchTwoThings1Prop <: SchTwoThings begin
  prop::Attr(Th1,Property)
end
@acset_type TwoThings1Prop(SchTwoThings1Prop)
Agg = @migration SchTwoThings1Prop SchTwoThings2Prop begin
  Th1 => Th1
  Th2 => Th2
  Property => Property
  f => f
  prop => x -> sum([prop(i) for i in dom(f) if f(i)==x])
end
X = @acset TwoThings2Prop{Float64} begin
  Th1 = 5
  Th2 = 10
  f = [2,4,4,4,10]
  prop = map(x->1.0,1:10)
end
Y = migrate(TwoThings1Prop,X,Agg)
@test subpart(Y,1:5,:prop) == [0.,1.,0.,3.,0.]
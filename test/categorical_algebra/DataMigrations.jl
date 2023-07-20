module TestDataMigrations
using Test

using Catlab.GATs, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Programs.DiagrammaticPrograms

@present SchSet(FreeSchema) begin
  X::Ob
end
@acset_type AcsetSet(SchSet)

@present SchDDS <: SchSet begin
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

# Contravariant migration
#########################

# Pullback migration
#-------------------

h = Graph(3)
add_parts!(h, :E, 3, src = [1,2,3], tgt = [2,3,1])

# Identity data migration.
@test h == migrate(Graph, h, Dict(:V => :V, :E => :E),
                   Dict(:src => :src, :tgt => :tgt))

# Migrate DDS → Graph.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,1])
X = SchDDS[:X]
@test h == migrate(Graph, dds, Dict(:V => :X, :E => :X),
                   Dict(:src => id(X), :tgt => :Φ))

h2 = copy(h)
migrate!(h2, dds, Dict(:V => :X, :E => :X),
                  Dict(:src => id(X), :tgt => :Φ))
@test h2 == ob(coproduct(h, h))

# Migrate DDS → DDS by advancing four steps.
@test dds == migrate(DDS, dds, Dict(:X => :X),
                     Dict(:Φ => [:Φ, :Φ, :Φ, :Φ]))

@present SchLabeledDDS <: SchDDS begin
  Label::AttrType
  label::Attr(X, Label)
end
@acset_type LabeledDDS(SchLabeledDDS, index=[:Φ, :label])

S, ϕ, Label, label = generators(SchLabeledDDS)
V, E, s, t, Weight, weight = generators(SchWeightedGraph)

ldds = LabeledDDS{Int}()
add_parts!(ldds, :X, 4, Φ=[2,3,4,1], label=[100, 101, 102, 103])

wg = WeightedGraph{Int}(4)
add_parts!(wg, :E, 4, src=[1,2,3,4], tgt=[2,3,4,1], weight=[101, 102, 103, 100])

@test wg == migrate(WeightedGraph{Int}, ldds,
  Dict(:V => :X, :E => :X, :Weight => :Label),
  Dict(:src => id(S), :tgt => :Φ, :weight => [:Φ, :label]))

@test Presentation(Graph(1)) == SchGraph
@test Presentation(ldds) == SchLabeledDDS

F = FinFunctor(
  Dict(V => S, E => S, Weight => Label),
  Dict(s => id(S), t => ϕ, weight => compose(ϕ, label)),
  SchWeightedGraph, SchLabeledDDS
)
ΔF = DataMigrationFunctor(F, LabeledDDS{Int}, WeightedGraph{Int})
@test wg == ΔF(ldds)

idF = id(FinCat(SchLabeledDDS))
@test ldds == migrate(LabeledDDS{Int}, ldds, DataMigration(idF))

# Conjunctive migration
#----------------------

# Graph whose edges are paths of length 2.
V, E, src, tgt = generators(SchGraph)
C = FinCat(SchGraph)
F_V = FinDomFunctor([V], FinCat(1), C)
F_E = FinDomFunctor(FreeDiagram(Cospan(tgt, src)), C)
M = DataMigration(FinDomFunctor(Dict(V => Diagram{op}(F_V),
                       E => Diagram{op}(F_E)),
                  Dict(src => DiagramHom{op}([(1, src)], F_E, F_V),
                       tgt => DiagramHom{op}([(2, tgt)], F_E, F_V)), C))
@test M isa DataMigrations.ConjSchemaMigration
g = path_graph(Graph, 5)
H = migrate(g, M, tabular=true)
@test length(H(V)) == 5
@test length(H(E)) == 3
@test H(src)((x1=2, x2=3, x3=3)) == (x1=2,)
@test H(tgt)((x1=2, x2=3, x3=3)) == (x1=4,)

# Same migration, but defining using the `@migration` macro.
M = @migration SchGraph SchGraph begin
  V => V
  E => @join begin
    v::V
    (e₁, e₂)::E
    tgt(e₁) == v
    src(e₂) == v
  end
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
end
F = functor(M)
H = migrate(g, M, tabular=true)
@test length(H(V)) == 5
@test length(H(E)) == 3
@test H(src)((v=3, e₁=2, e₂=3)) == (V=2,)
@test H(tgt)((v=3, e₁=2, e₂=3)) == (V=4,)

h = migrate(Graph, g, M)
@test (nv(h), ne(h)) == (5, 3)
@test sort!(collect(zip(h[:src], h[:tgt]))) == [(1,3), (2,4), (3,5)]

h = Graph(5)
migrate!(h, g, M)
@test (nv(h), ne(h)) == (10, 3)
@test sort!(collect(zip(h[:src], h[:tgt]))) == [(6,8), (7,9), (8,10)]

# Weighted graph whose edges are path of length 2 with equal weight.
F = @migration SchWeightedGraph SchWeightedGraph begin
  V => V
  E => @join begin
    v::V; (e₁, e₂)::E; w::Weight
    tgt(e₁) == v
    src(e₂) == v
    weight(e₁) == w
    weight(e₂) == w
  end
  Weight => Weight
  src => e₁ ⋅ src
  tgt => e₂ ⋅ tgt
  weight => w
end
g = path_graph(WeightedGraph{Float64}, 6, E=(weight=[0.5,0.5,1.5,1.5,1.5],))
h = migrate(WeightedGraph{Float64}, g, F)
@test (nv(h), ne(h)) == (6, 3)
@test sort!(collect(zip(h[:src], h[:tgt], h[:weight]))) ==
  [(1,3,0.5), (3,5,1.5), (4,6,1.5)]

# Graph whose vertices are paths of length 2 and edges are paths of length 3.
g = path_graph(Graph, 6)
h = @migrate Graph g begin
  V => @join begin
    v::V
    (e₁, e₂)::E
    (t: e₁ → v)::tgt
    (s: e₂ → v)::src
  end
  E => @join begin
    (v₁, v₂)::V
    (e₁, e₂, e₃)::E
    (t₁: e₁ → v₁)::tgt
    (s₁: e₂ → v₁)::src
    (t₂: e₂ → v₂)::tgt
    (s₂: e₃ → v₂)::src
  end
  src => (v => v₁; e₁ => e₁; e₂ => e₂; t => t₁; s => s₁)
  tgt => (v => v₂; e₁ => e₂; e₂ => e₃; t => t₂; s => s₂)
end
@test h == path_graph(Graph, 4)

# Bouquet graph on a set.
set = @acset AcsetSet begin X = 5 end
g = @migrate Graph set begin
  V => @unit
  E => X
end
g′ = @acset Graph begin
  V = 1
  E = 5
  src = [1,1,1,1,1]
  tgt = [1,1,1,1,1]
end
@test g == g′

# Gluing migration
#-----------------

# Free reflexive graph on a graph.
g = cycle_graph(Graph, 5)
h = @migrate ReflexiveGraph g begin
  V => V
  E => @cases (v::V; e::E)
  src => (e => src)
  tgt => (e => tgt)
  refl => v
end
@test h == cycle_graph(ReflexiveGraph, 5)

# Free symmetric graph on a graph.
g = star_graph(Graph, 5)
h = @migrate SymmetricGraph g begin
  V => V
  E => @cases (fwd::E; rev::E)
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  inv => (fwd => rev; rev => fwd)
end
@test h == star_graph(SymmetricGraph, 5)

# Free symmetric weighted graph on a weighted graph.
weights = range(0, 1, length=5)
g = star_graph(WeightedGraph{Float64}, 6, E=(weight=weights,))
h = @migrate SymmetricWeightedGraph g begin
  V => V
  E => @cases (fwd::E; rev::E)
  Weight => Weight
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  inv => (fwd => rev; rev => fwd)
  weight => (fwd => weight; rev => weight)
end
h′ = star_graph(SymmetricWeightedGraph{Float64}, 6)
h′[:weight] = vcat(weights, weights)
@test h == h′

# Free symmetric reflexive graph on a reflexive graph.
g = star_graph(ReflexiveGraph, 5)
h = @migrate SymmetricReflexiveGraph g begin
  V => V
  E => @glue begin
    (fwd, rev)::E
    v::V
    (refl_fwd: v → fwd)::refl
    (refl_rev: v → rev)::refl
  end
  src => (fwd => src; rev => tgt)
  tgt => (fwd => tgt; rev => src)
  refl => v
  inv => begin
    fwd => rev; rev => fwd; v => v;
    refl_fwd => refl_rev; refl_rev => refl_fwd
  end
end
@test is_isomorphic(h, star_graph(SymmetricReflexiveGraph, 5))

# Discrete graph on set.
set = @acset AcsetSet begin X = 5 end
g = @migrate Graph set begin
  V => X
  E => @empty
end
@test g == Graph(5)

# Gluc migration
#---------------

# Graph with edges that are paths of length <= 2.
g = path_graph(Graph, 4)
h = @migrate Graph g begin
  V => V
  E => @cases begin
    v => V
    e => E
    path => @join begin
      v::V
      (e₁, e₂)::E
      tgt(e₁) == v
      src(e₂) == v
    end
  end
  src => (e => src; path => e₁⋅src)
  tgt => (e => tgt; path => e₂⋅tgt)
end
h′ = @acset Graph begin
  V = 4
  E = 9
  src = [1,2,3,4, 1,2,3, 1,2]
  tgt = [1,2,3,4, 2,3,4, 3,4]
end
@test h == h′

# Sigma migration
#################

V1B, V2B, EB = generators(SchUndirectedBipartiteGraph, :Ob)
srcB, tgtB = generators(SchUndirectedBipartiteGraph, :Hom)

VG, EG = generators(SchGraph, :Ob)
srcG, tgtG = generators(SchGraph, :Hom)

F = FinFunctor(
  Dict(V1B => VG, V2B => VG, EB => EG),
  Dict(srcB => srcG, tgtB => tgtG),
  SchUndirectedBipartiteGraph, SchGraph
)
idF = id(FinCat(SchGraph))

ΣF = SigmaMigrationFunctor(F, UndirectedBipartiteGraph, Graph)
X = UndirectedBipartiteGraph()

Y = ΣF(X)
@test nparts(Y, :V) == 0
@test nparts(Y, :E) == 0

X = @acset UndirectedBipartiteGraph begin
  V₁ = 4
  V₂ = 3
  E = 4
  src = [1,2,2,3]
  tgt = [1,1,2,3]
end

Yd = ΣF(X; return_unit=true)
Y = Graph(codom(Yd))
α = diagram_map(Yd)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0
@test isempty(collect(α[:V₁]) ∩ collect(α[:V₂]))

@test SigmaMigrationFunctor(idF, Graph, Graph)(Y) == Y

# Sigma migrations with attributes
#---------------------------------

# Identity migration on weighted graphs.
Y = @acset WeightedGraph{Symbol} begin
  V=2; E=2; Weight=1; src=1; tgt=[1,2]; weight=[AttrVar(1), :X]
end
ΣF = SigmaMigrationFunctor(id(FinCat(SchWeightedGraph)),
                           WeightedGraph{Symbol}, WeightedGraph{Symbol})
@test is_isomorphic(ΣF(Y),Y)

# Less trivial example.
@present SchTwoThings(FreeSchema) begin
  Th1::Ob
  Th2::Ob
  Property::AttrType
  # The ID attribute keeps track of combinatorial objects as their
  # non-meaningful integer IDs may be modified by the chase.
  ID::AttrType
  f::Hom(Th1,Th2)
  id::Attr(Th1,ID)
end
@present SchThing1WithProp <: SchTwoThings begin
  prop::Attr(Th1,Property)
end
@acset_type Thing1WithProp(SchThing1WithProp)
@present SchThing2WithProp <: SchTwoThings begin
  prop::Attr(Th2,Property)
end
@acset_type Thing2WithProp(SchThing2WithProp)

X = @acset Thing2WithProp{Bool,String} begin
  Th1 = 2
  Th2 = 4
  f = [1,3]
  prop = [false,false,true,true]
  id = ["ffee cup","doughnut"]
end

Y = @acset Thing1WithProp{Bool,String} begin
  Th1 = 2
  Th2 = 4
  f = [1,3]
  prop = [false,true]
  id = ["ffee cup","doughnut"]
end
C1,C2 = FinCat(SchThing1WithProp),FinCat(SchThing2WithProp)
th1,th2,property,ID = ob_generators(C1)
f1,id1,prop1 = hom_generators(C1)
f2,id2,prop2 = hom_generators(C2)

F = FinFunctor(
  Dict(th1 => th1, th2 => th2, property => property,ID=>ID),
  Dict(f1 => f2, prop1 => [f2, prop2],id1=>id2),
  SchThing1WithProp, SchThing2WithProp
)

ΔF = DataMigrationFunctor(F, Thing2WithProp{Bool,String}, Thing1WithProp{Bool,String})
ΣF = SigmaMigrationFunctor(F, Thing1WithProp{Bool,String}, Thing2WithProp{Bool,String})

YY = ΔF(X)
XX = ΣF(Y)
@test YY == Y
@test incident(XX,false,[:f,:prop]) == incident(XX,"ffee cup",:id)

# Terminal map
#-------------
@present ThSpan(FreeSchema) begin
  (L1, L2, A)::Ob
  l1::Hom(A, L1)
  l2::Hom(A, L2)
end
@acset_type Span(ThSpan, index=[:l1, :l2])

X = @acset Span begin
  L1 = 3
  L2 = 4
  A = 3
  l1 = [1,1,2]
  l2 = [1,2,3]
end

@present ThInitial(FreeSchema) begin
  I::Ob
end
@acset_type Initial(ThInitial)

L1, L2, A = generators(ThSpan, :Ob)
l1, l2 = generators(ThSpan, :Hom)
I = generators(ThInitial)[1]

bang = FinFunctor(
  Dict(L1 => I, L2 => I, A => I),
  Dict(l1 => id(I), l2 => id(I)),
  ThSpan, ThInitial
)

Σbang = SigmaMigrationFunctor(bang, Span, Initial)
Yd = Σbang(X; return_unit=true)
α = diagram_map(Yd)
@test length(unique([α[:A](1:2)...,α[:L1](1),α[:L2](1:2)...])) == 1
Y = Initial(codom(Yd))
@test nparts(Y, :I) == 4

# Map from terminal C 
#--------------------

V = FinFunctor(Dict(I => VG), Dict(), ThInitial, SchGraph)
E = FinFunctor(Dict(I => EG), Dict(), ThInitial, SchGraph)

Z = SigmaMigrationFunctor(V, Initial, Graph)(Y)
@test nparts(Z, :V) == 4
@test nparts(Z, :E) == 0

Z = SigmaMigrationFunctor(E, Initial, Graph)(Y)
expected = foldl(⊕,fill(path_graph(Graph,2), 4))  
@test is_isomorphic(Z,expected)

# Using the equations of the schema 
#----------------------------------
F = FinFunctor(
  Dict(:V => :V, :E=> :E),
  Dict(:src=>:src, :tgt=>:tgt),
  SchGraph, SchReflexiveGraph
)
G = path_graph(Graph,3)
Σ = SigmaMigrationFunctor(F, Graph, ReflexiveGraph)
expected = @acset ReflexiveGraph  begin 
  V=3; E=5; refl=1:3; src=[1,2,3,1,2]; tgt=[1,2,3,2,3] 
end 
@test is_isomorphic(Σ(G), expected)

# Sigma with attributes 
#----------------------

# Connected components must be monochromatic
@present SchWG <: SchGraph begin
  Color::AttrType
  color::Attr(V,Color)
  src ⋅ color == tgt ⋅ color
end
@acset_type WG(SchWG)

F = FinFunctor(Dict(:V => :V, :E=> :E), Dict(:src=>:src, :tgt=>:tgt), SchGraph, SchWG)
Σ = SigmaMigrationFunctor(F, Graph, WG{Float64})

G = path_graph(Graph,3) ⊕ Graph(1) # two connected components
expected = @acset WG{Float64} begin 
  V=4; E=2; Color=2; src=[2,3]; tgt=[3,1]; color=AttrVar.([1,1,1,2]) 
end

@test is_isomorphic(Σ(G), expected)
 
# Yoneda embedding
#-----------------

# Yoneda embedding for graphs (no attributes).
yV, yE = Graph(1), @acset(Graph, begin V=2;E=1;src=2;tgt=1 end)
@test representable(Graph, :V) == yV
@test is_isomorphic(representable(Graph, :E), yE)

y_Graph = yoneda(Graph)
@test ob_map(y_Graph, :V) == yV
@test is_isomorphic(ob_map(y_Graph, :E), yE)
@test Set(hom_map.(Ref(y_Graph), [:src,:tgt])) == Set(
  homomorphisms(yV, representable(Graph, :E)))

F = @migration SchGraph begin
  X => E
  (I, O) => V
  (i: X → I) => src
  (o: X → O) => tgt
end
G = colimit_representables(F, y_Graph) # Delta migration.
X = ob_map(G, :X)
@test is_isomorphic(X, yE)
i, o = hom_map(G, :i), hom_map(G, :o)
@test sort(only.(collect.([i[:V],o[:V]]))) == [1,2]

F = @migration SchGraph begin
  X => @join begin
    (e₁, e₂)::E
    tgt(e₁) == src(e₂)
  end
  (I, O) => V
  (i: X → I) => src(e₁)
  (o: X → O) => tgt(e₂)
end
G = colimit_representables(F, y_Graph) # Conjunctive migration.
X = ob_map(G, :X)
@test is_isomorphic(X, path_graph(Graph, 3))
i, o = hom_map(G, :i), hom_map(G, :o)
@test isempty(inneighbors(X, only(collect(i[:V]))))
@test isempty(outneighbors(X, only(collect(o[:V]))))

# Yoneda embedding for weights graphs (has attributes).
WGF = WeightedGraph{Float64}
yV, yE = WGF(1), @acset(WGF, begin 
  V=2;E=1;Weight=1;src=2;tgt=1; weight=[AttrVar(1)]
end)
@test representable(WGF, SchWeightedGraph, :V) == yV
@test is_isomorphic(representable(WGF, SchWeightedGraph, :E), yE)

yWG = yoneda(WGF)

F = @migration SchWeightedGraph begin
  X => E
  (I, O) => V
  (i: X → I) => src
  (o: X → O) => tgt
end
G = colimit_representables(F, yWG) # Delta migration.
X = ob_map(G, :X)
@test is_isomorphic(X, yE)
i, o = hom_map(G, :i), hom_map(G, :o)
@test sort(only.(collect.([i[:V],o[:V]]))) == [1,2]


d = @migration(SchWeightedGraph, begin
    I => @join begin
      (e1,e2,e3)::E
      (w1,w3)::Weight
      src(e1) == src(e2)      
      weight(e1) == w1
      w1 == 1.9     
      weight(e2) == 1.8 
      weight(e3) == w3
    end
end)

expected = @acset WeightedGraph{Float64} begin
  V=5; E=3; Weight=1; src=[1,1,3]; tgt=[2,4,5]; weight=[1.8,1.9,AttrVar(1)]
end
@test is_isomorphic(ob_map(colimit_representables(d, yWG), :I), expected)


# Subobject classifier
######################
# Graph and ReflGraph have 'same' subobject classifier
ΩG,_ = subobject_classifier(Graph, SchGraph)
ΩrG,_ = subobject_classifier(ReflexiveGraph, SchReflexiveGraph)
F = FinFunctor(Dict(:V=>:V, :E=>:E), Dict(:src=>:src, :tgt=>:tgt), 
               SchGraph, SchReflexiveGraph)
ΔF = DataMigrationFunctor(F, ReflexiveGraph, Graph)
@test is_isomorphic(ΩG, ΔF(ΩrG))

# Searching for maps into the subobject classifier is much faster than 
# enumerating them via `subobject_graph`
G = (star_graph(Graph, 2)⊗path_graph(Graph, 3))
@test length(homomorphisms(G, ΩG)) == length(subobject_graph(G)[2])

@present SchDDS42(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
  Φ⋅Φ⋅Φ⋅Φ == Φ⋅Φ
end
@acset_type DDS42(SchDDS42, index=[:Φ])
ΩDDs, _ = subobject_classifier(DDS42, SchDDS42)
@test is_isomorphic(ΩDDs, @acset DDS42 begin X=4; Φ=[1,3,4,4] end)

# Internal Hom
##############
G = ReflexiveGraph(2)
F = path_graph(ReflexiveGraph, 2)
Fᴳ,_ = internal_hom(G,F, SchReflexiveGraph)
Z = apex(terminal(ReflexiveGraph)) ⊕ path_graph(ReflexiveGraph, 3)
@test length(homomorphisms(Z, Fᴳ)) == length(homomorphisms(Z ⊗ G, F)) # 64

G = @acset DDS42 begin X=3; Φ=[2,3,3] end
F = @acset DDS42 begin X=4; Φ=[2,2,4,4] end
Fᴳ,_ = internal_hom(G,F, SchDDS42)
Z = @acset DDS42 begin X=5; Φ=[2,3,4,3,4] end
@test length(homomorphisms(Z, Fᴳ)) == length(homomorphisms(Z ⊗ G, F)) # 1024

end # module

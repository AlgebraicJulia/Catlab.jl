module TestDataMigration
using Test
using Catlab.CSetDataStructures
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheoryWeightedGraph
using Catlab.Graphs.BipartiteGraphs: TheoryUndirectedBipartiteGraph
using Catlab.Theories
using Catlab.Theories: id, compose
using Catlab.Present


# Pullback data migration
###########################

@present TheoryDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

@abstract_acset_type AbstractDDS
@acset_type DDS(TheoryDDS, index=[:Φ]) <: AbstractDDS

h = Graph(3)
add_parts!(h, :E, 3, src = [1,2,3], tgt = [2,3,1])

# Identity data migration.
#-------------------------
@test h == Graph(h, Dict(:V => :V, :E => :E),
                    Dict(:src => :src, :tgt => :tgt))

# Migrate DDS → Graph.
#---------------------
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,1])
X = TheoryDDS[:X]
@test h == Graph(dds, Dict(:V => :X, :E => :X),
                 Dict(:src => id(X), :tgt => :Φ))

h2 = copy(h)
migrate!(h2, dds, Dict(:V => :X, :E => :X),
                  Dict(:src => id(X), :tgt => :Φ))
@test h2 == ob(coproduct(h, h))

# Migrate DDS → DDS by advancing four steps.
#-------------------------------------------
@test dds == DDS(dds, Dict(:X => :X),
                      Dict(:Φ => [:Φ, :Φ, :Φ, :Φ]))

@present TheoryLabeledDDS <: TheoryDDS begin
  Label::AttrType
  label::Attr(X, Label)
end

@acset_type LabeledDDS(TheoryLabeledDDS, index=[:Φ, :label])

S, ϕ, Label, label = generators(TheoryLabeledDDS)
V, E, s, t, Weight, weight = generators(TheoryWeightedGraph)

ldds = LabeledDDS{Int}()
add_parts!(ldds, :X, 4, Φ=[2,3,4,1], label=[100, 101, 102, 103])

wg = WeightedGraph{Int}(4)
add_parts!(wg, :E, 4, src=[1,2,3,4], tgt=[2,3,4,1], weight=[101, 102, 103, 100])

@test wg == WeightedGraph{Int}(ldds,
  Dict(:V => :X, :E => :X),
  Dict(:src => id(S), :tgt => :Φ, :weight => [:Φ, :label]))

@test Presentation(Graph(1)) == TheoryGraph
@test Presentation(ldds) == TheoryLabeledDDS


F = Functor(
  Dict(V => S, E => S),
  Dict(s => id(S), t => ϕ, weight => compose(ϕ, label)),
  TheoryWeightedGraph, TheoryLabeledDDS
)

ΔF = Delta(F, LabeledDDS, WeightedGraph)
@test dom(ΔF) == LabeledDDS
@test codom(ΔF) == WeightedGraph

@test wg == WeightedGraph{Int}(ldds, F)

idF = Functor(
  Dict(X => X, Label => Label),
  Dict(ϕ => ϕ, label => label),
  TheoryLabeledDDS, TheoryLabeledDDS
)

@test ldds == LabeledDDS{Int}(ldds, idF)


# Left Pushforward data migration
#################################
Σ = Sigma

# Bipartite graph to graph
#-------------------------

V1B, V2B, EB = generators(TheoryUndirectedBipartiteGraph, :Ob)
srcB, tgtB = generators(TheoryUndirectedBipartiteGraph, :Hom)

VG, EG = generators(TheoryGraph, :Ob)
srcG, tgtG = generators(TheoryGraph, :Hom)

# Merge the two kinds of vertices into one (disjointly)
F = Functor(
    Dict(V1B => VG, V2B => VG, EB => EG),
    Dict(srcB => srcG, tgtB => tgtG),
    TheoryUndirectedBipartiteGraph, TheoryGraph
)

# Identity
idF = Functor(
  Dict(VG => VG, EG => EG),
  Dict(srcG => srcG, tgtG => tgtG),
  TheoryGraph, TheoryGraph
)

# Test Implementation 1
ΣF =  Σ(F, UndirectedBipartiteGraph, Graph)
@test dom(ΣF) == UndirectedBipartiteGraph
@test codom(ΣF) == Graph
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
Y = ΣF(X)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0

@test Σ(idF, Graph, Graph)(Y) == Y


# Test implementation 2

# Chasing an empty instance yields an empty instance in this case
@test chase(F, UndirectedBipartiteGraph(), Graph()) == Graph()

Y = chase(F, X, Graph())
chase_res = Graph(7)
add_edges!(chase_res, [1,2,2,3],[5,5,6,7])
@test is_isomorphic(chase_res, Y)


@test is_isomorphic(Y, chase(idF, Y, Graph())) # chasing valid instance on id

# Connected components of span
#-----------------------------

@present ThSpan(FreeSchema) begin
  (L1, L2, A)::Ob
  l1::Hom(A, L1)
  l2::Hom(A, L2)
end

@acset_type Span(ThSpan, index=[:l1, :l2])

L1, L2, A = generators(ThSpan, :Ob)
l1, l2 = generators(ThSpan, :Hom)

X = @acset Span begin
  L1 = 3
  L2 = 4
  A = 3
  l1 = [1,1,2]
  l2 = [1,2,3]
end

@present ThInit(FreeSchema) begin
  I::Ob
end
@acset_type Init(ThInit)

I = generators(ThInit)[1]

# Collect the connected components across all three sets
bang = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(L1 => I, L2 => I, A => I),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(l1 => id(I), l2 => id(I)),
  ThSpan, ThInit
)

# Test Implementation 1
Σbang = Σ(bang, Span, Init)
Y = Σbang(X)
@test nparts(Y, :I) == 4

# Test implementation 2
Σbang = chase(bang, X, Init()) # Σ(bang, Span, Init)
@test nparts(Σbang, :I) == 4


# Init -> Graph
#-----------------

# Interpret points as vertices
vertex = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(I => VG),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(),
  ThInit, TheoryGraph
)
# Interpret points as edges, with arbitrary src/tgt
edge = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(I => EG),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(),
  ThInit, TheoryGraph
)
I4 = Init()
add_parts!(I4, :I, 4)

# Test implementation 1
Z = Σ(vertex, I4, Graph)(Y)
@test nparts(Z, :V) == 4
@test nparts(Z, :E) == 0

Z = Σ(edge, I4, Graph)(Y)
@test nparts(Z, :V) == 8
@test nparts(Z, :E) == 4
@test Z[:src] ∪ Z[:tgt] == 1:8

# Test implementation 2
@test chase(vertex, I4, Graph()) == Graph(4)
chase_res = Graph(8)
add_edges!(chase_res, [1,2,3,4], [5,6,7,8])
@test is_isomorphic(chase_res, chase(edge, I4, Graph()))

# Non-acyclic example
#--------------------
@present ThCompany(FreeSchema) begin
  Employee::Ob
  Department::Ob
  Str::Ob
  name::Hom(Employee, Str)
  manager::Hom(Employee, Employee)
  works_in::Hom(Employee, Department)
  secretary::Hom(Department, Employee)

  # Managers work in same department
  compose(manager, works_in) == works_in

  # The secretary of a department works in that department.
  compose(secretary, works_in) == id(Department)

  # Everyone's their own boss
  manager == id(Employee)

end

@acset_type Company(ThCompany)

ex = @acset Company begin
  Employee=3
  Department = 1
  Str = 3
  name = [1,2,3]
  manager = [1,2,3]
  works_in = [1,1,1]
  secretary = [1]
end

# add one arbitrary employee to the company => induces a new dept + secretary
chase_res = @acset Company begin
  Employee= 3 + 2
  Department = 1 + 1
  Str = 3 + 2
  name = [1,2,3, 4,5]
  manager = [1,2,3, 4,5]
  works_in = [1,1,1, 2,2]
  secretary = [1, 4]
end


(EG, _, _) = generators(ThCompany, :Ob)

I1 = @acset Init begin I=1 end
tf = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(I => EG),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(),
  ThInit, ThCompany
)

# Example of chasing with a non-empty codomain instance
@test is_isomorphic(chase_res, chase(tf, I1, ex))

# "Fast Left Kan Extensions Using The Chase" running example
#-----------------------------------------------------------
@present ThC(FreeSchema) begin
  (TA′, Faculty′, Student′)::Ob
  isTF′::Hom(TA′,Faculty′)
  isTS′::Hom(TA′, Student′)
end

@present ThD(FreeSchema) begin
  (TA, Faculty, Student, Person)::Ob
  isTF::Hom(TA,Faculty)
  isTS::Hom(TA, Student)
  isFP::Hom(Faculty, Person)
  isSP::Hom(Student, Person)
  compose(isTF, isFP) == compose(isTS, isSP)
end

@acset_type C(ThC)
@acset_type D(ThD)

GT_, GF_, GS_ = generators(ThC, :Ob)
GT, GF, GS, _ = generators(ThD, :Ob)
GTF_, GTS_ = generators(ThC, :Hom)
GTF, GTS,_, _ = generators(ThD, :Hom)

F = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(GT_ => GT, GF_=>GF, GS_=>GS),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(GTF_=>GTF, GTS_=>GTS),
  ThC, ThD
)
I = @acset C begin
  Faculty′ = 5
  Student′ = 4
  TA′ = 2
  isTF′ = [1,2]
  isTS′ = [1,3]
end

chase_res = @acset D begin
  Faculty = 5
  Student = 4
  TA = 2
  Person = 7
  isTF = [1,2]
  isTS = [1,2]
  isFP = [1,2,3,4,5]
  isSP = [1,2,6,7]
end

@test is_isomorphic(chase(F,I, D()), chase_res)

end #module
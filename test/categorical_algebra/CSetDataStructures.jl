module TestCSetDataStructures
using Test

using Catlab: @present, generator
using Catlab.Theories: compose, id
using Catlab.CSetDataStructures
using Tables

# Discrete dynamical systems
############################

@present TheoryDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

@abstract_acset_type AbstractDDS
@acset_type DDS(TheoryDDS, index=[:Φ]) <: AbstractDDS
@test DDS <: AbstractDDS
@test DDS <: StructACSet
@test DDS <: StructCSet
@test DDS <: ACSet

dds = DDS()
@test keys(tables(dds)) == (:X,)
@test nparts(dds, :X) == 0
@test add_part!(dds, :X) == 1
@test nparts(dds, :X) == 1
@test incident(dds, 1, :Φ) == []

set_subpart!(dds, 1, :Φ, 1)
@test subpart(dds, 1, :Φ) == 1
@test incident(dds, 1, :Φ) == [1]

@test add_part!(dds, :X, Φ=1) == 2
@test add_part!(dds, :X, Φ=1) == 3
@test subpart(dds, :Φ) == [1,1,1]
@test subpart(dds, [2,3], :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2,3]

@test has_part(dds, :X)
@test !has_part(dds, :nonpart)
@test has_part(dds, :X, 3)
@test !has_part(dds, :X, 4)
@test has_part(dds, :X, 1:5) == [true, true, true, false, false]

@test has_subpart(dds, :Φ)
@test !has_subpart(dds, :nonsubpart)
@test_throws ArgumentError subpart(dds, 1, :nonsubpart)
@test_throws ArgumentError incident(dds, 1, :nonsuppart)
@test_throws ArgumentError set_subpart!(dds, 1, :nonsubpart, 1)

# Deletion.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,3])
rem_part!(dds, :X, 2)
@test nparts(dds, :X) == 2
@test subpart(dds, :Φ) == [0,2]
@test incident(dds, 1, :Φ) == []
@test incident(dds, 2, :Φ) == [2]
rem_part!(dds, :X, 2)
@test nparts(dds, :X) == 1
@test subpart(dds, :Φ) == [0]
rem_part!(dds, :X, 1)
@test nparts(dds, :X) == 0

dds = DDS()
add_parts!(dds, :X, 4, Φ=[2,3,3,4])
@test_throws ErrorException rem_parts!(dds, :X, [4,1])
rem_parts!(dds, :X, [1,4])
@test subpart(dds, :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2]
@test incident(dds, 2, :Φ) == []

# Pretty printing.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,3])
s = sprint(show, dds)
@test contains(s, "DDS:")
@test contains(s, "X = 1:3")
@test contains(s, "Φ : X → X = ")
s = sprint(show, dds, context=:compact=>true)
@test contains(s, "DDS")
@test !contains(s, "\n")
@test contains(s, "X = 3")

s = sprint(show, MIME"text/plain"(), dds)
@test contains(s, "DDS")
@test contains(s, "X = 1:3")
@test contains(s, "│ X │")

s = sprint(show, MIME"text/html"(), dds)
@test startswith(s, "<div class=\"c-set\">")
@test contains(s, "<table>")
@test endswith(rstrip(s), "</div>")

# Special case of pretty print: empty table.
empty_dds = DDS()
@test !isempty(sprint(show, empty_dds))
@test !isempty(sprint(show, MIME"text/plain"(), empty_dds))
@test !isempty(sprint(show, MIME"text/html"(), empty_dds))

# Error handling when adding parts.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[1,1,1])
@test_throws AssertionError add_part!(dds, :X, Φ=5)
@test nparts(dds, :X) == 3
@test subpart(dds, :Φ) == [1,1,1]
@test_throws AssertionError add_parts!(dds, :X, 2, Φ=[3,6])
@test nparts(dds, :X) == 3
@test incident(dds, 3, :Φ) == []

# Incidence without indexing.
@acset_type UnindexedDDS(TheoryDDS)
dds = UnindexedDDS()
add_parts!(dds, :X, 4, Φ=[3,3,4,4])
# @test isempty(keys(dds.indices))
@test incident(dds, 3, :Φ) == [1,2]
@test incident(dds, 4, :Φ) == [3,4]

# Dendrograms
#############

# Strictly speaking, this data structure is not a single dendrogram but a forest
# of dendrograms (whose roots are the elements fixed under the `parent` map) and
# in order to be valid dendrograms, there must be no nontrivial cycles and the
# `height` map must satisfy `compose(parent, height) ≥ height` pointwise.

@present TheoryDendrogram(FreeSchema) begin
  X::Ob
  R::AttrType
  parent::Hom(X,X)
  height::Attr(X,R)
end

@abstract_acset_type AbstractDendrogram

@acset_type Dendrogram(TheoryDendrogram, index=[:parent]) <: AbstractDendrogram

@test Dendrogram <: AbstractDendrogram
@test Dendrogram <: ACSet
@test Dendrogram{Real} <: AbstractDendrogram{S,Tuple{Real}} where {S}

d = Dendrogram{Int}()
add_parts!(d, :X, 3, height=0)
add_parts!(d, :X, 2, height=[10,20])
set_subpart!(d, 1:3, :parent, 4)
set_subpart!(d, [4,5], :parent, 5)

@test nparts(d, :X) == 5
@test subpart(d, 1:3, :parent) isa SubArray{Int,1}
@test subpart(d, 1:3, :parent) == [4,4,4]
@test subpart(d, 4, :parent) == 5
@test subpart(d, :, :parent) == [4,4,4,5,5]
@test incident(d, 4, :parent) == [1,2,3]
@test incident(d, 4:5, :parent) isa SubArray{Vector{Int},1}
@test incident(d, 4:5, :parent) == [[1,2,3], [4,5]]
@test has_subpart(d, :height)
@test subpart(d, [1,2,3], :height) == [0,0,0]
@test subpart(d, 4, :height) == 10
@test subpart(d, :, :height) == [0,0,0,10,20]

# Chained accessors.
@test subpart(d, 3, [:parent, :parent]) == 5
@test subpart(d, 3, [:parent, :height]) == 10
@test incident(d, 5, [:parent, :parent]) == [1,2,3,4,5]
@test incident(d, 10, [:parent, :height]) == [1,2,3]

X, parent, height = TheoryDendrogram[[:X, :parent, :height]]
@test subpart(d, 3, parent) == 4
@test subpart(d, 3, compose(parent, height)) == 10
@test subpart(d, 3, id(X)) == 3
@test incident(d, 10, compose(parent, height)) == [1,2,3]
@test subpart(d, parent) == [4,4,4,5,5]
@test subpart(d, id(X)) == 1:5
@test subpart(d, compose(parent, height)) == [10,10,10,20,20]

# Indexing syntax.
@test d[3, :parent] == 4
@test d[3, [:parent, :height]] == 10
@test d[3:5, [:parent, :height]] == [10,20,20]
@test d[:, :parent] == [4,4,4,5,5]
d2 = copy(d)
d2[1, :parent] = 1
d2[2:3, :parent] = 2:3
@test d2[1:3, :parent] == 1:3
d2[1:3, :parent] = 4
@test d2 == d

# Copying parts.
d2 = Dendrogram{Int}()
copy_parts!(d2, d, X=[4,5])
@test nparts(d2, :X) == 2
@test subpart(d2, [1,2], :parent) == [2,2]
@test subpart(d2, [1,2], :height) == [10,20]

du = disjoint_union(d, d2)
@test nparts(du, :X) == 7
@test subpart(du, :parent) == [4,4,4,5,5,7,7]
@test subpart(du, :height) == [0,0,0,10,20,10,20]

# Pretty printing of data attributes.
s = sprint(show, d)
@test contains(s, "Dendrogram{Int64}:")
@test contains(s, "height : X → R = ")

s = sprint(show, MIME"text/plain"(), d)
@test contains(s, "Dendrogram{Int64}")

# Allow type inheritance for data attributes.
d_abs = Dendrogram{Number}()
add_parts!(d_abs, :X, 2, height=[10.0, 4])
@test subpart(d_abs, :height) == [10.0, 4]

# Tables interface
td = tables(d)
@test keys(td) == (:X,)
@test Tables.istable(td.X) == true
cols = Tables.columns(td.X)
@test Tables.columnnames(cols) == (:parent, :height)
@test Tables.getcolumn(cols, :parent) == [4,4,4,5,5]
@test Tables.getcolumn(cols, 1) == [4,4,4,5,5]
rows = [Tables.rows(td.X)...]
@test length(rows) == 5
@test Tables.columnnames(rows[1]) == (:parent, :height)
@test Tables.getcolumn(rows[1], :parent) == 4
@test Tables.getcolumn(rows[1], :height) == 0
@test Tables.getcolumn(rows[1], 1) == 4

# Dendrograms with leaves
#------------------------

@present TheoryLDendrogram <: TheoryDendrogram begin
  L::Ob
  leafparent::Hom(L,X)
end

@acset_type LDendrogram(TheoryLDendrogram, index=[:parent, :leafparent]) <: AbstractDendrogram

# Copying between C-sets and C′-sets with C != C′.
ld = LDendrogram{Int}()
copy_parts!(ld, d)
@test nparts(ld, :L) == 0
@test subpart(ld, :parent) == subpart(d, :parent)

add_parts!(ld, :L, 3, leafparent=[2,3,4])
@test subpart(ld, :leafparent) == [2,3,4]
d′ = Dendrogram{Int}()
copy_parts!(d′, ld)
@test d′ == d

# Subsets
#########

# A set together with a subset, with unique indexing for fast membership checks.

@present TheorySubset(FreeSchema) begin
  (Set, Sub)::Ob
  ι::Hom(Sub, Set)
end
@acset_type Subset(TheorySubset, unique_index=[:ι])

Base.in(x, X::Subset) = incident(X, x, :ι) != 0

A = Subset()
add_parts!(A, :Set, 2)
add_part!(A, :Sub, ι=1)
B = Subset()
add_parts!(B, :Set, 2)
add_part!(B, :Sub, ι=2)
@test 1 ∈ A && 2 ∉ A
@test 1 ∉ B && 2 ∈ B

# Labeled sets
##############

# The simplest example of a C-set with a data attribute, to test data indexing.

@present TheoryLabeledSet(FreeSchema) begin
  X::Ob
  Label::AttrType
  label::Attr(X,Label)
end

# Labeled sets with index
#------------------------

@acset_type IndexedLabeledSet(TheoryLabeledSet, index=[:label])

lset = IndexedLabeledSet{Symbol}()
# @test keys(lset.indices) == (:label,)
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == [1]
@test isempty(incident(lset, :nonkey, :label))

add_part!(lset, :X, label=:foo)
@test incident(lset, :foo, :label) == [1,3]
set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, [:foo,:baz], :label) == [[3],[1]]
set_subpart!(lset, 3, :label, :biz)
@test incident(lset, :foo, :label) == []

# Labeled set with compound label (tuple).
lset = IndexedLabeledSet{Tuple{Int,Int}}()
add_parts!(lset, :X, 2, label=[(1,1), (1,2)])
@test incident(lset, (1,2), :label) == [2]

# Deletion with indexed data attribute.
lset = IndexedLabeledSet{Symbol}()
add_parts!(lset, :X, 3, label=[:foo, :foo, :bar])
rem_part!(lset, :X, 1)
@test subpart(lset, :label) == [:bar, :foo]
@test incident(lset, [:foo, :bar], :label) == [[2], [1]]

# Deletion with unitialized data attribute.
lset = IndexedLabeledSet{Symbol}()
add_part!(lset, :X)
rem_part!(lset, :X, 1)
@test nparts(lset, :X) == 0

# Pretty-printing with unitialized data attribute.
lset = IndexedLabeledSet{Symbol}()
add_part!(lset, :X)
@test contains(sprint(show, lset), "#undef")
@test contains(sprint(show, MIME"text/plain"(), lset), "#undef")
@test contains(sprint(show, MIME"text/html"(), lset), "#undef")

# Labeled sets with unique index
#-------------------------------

@acset_type UniqueIndexedLabeledSet(TheoryLabeledSet, unique_index=[:label])

lset = UniqueIndexedLabeledSet{Symbol}()
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == 1
@test incident(lset, [:foo,:bar], :label) == [1,2]
@test incident(lset, :nonkey, :label) == 0

set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, :baz, :label) == 1
@test incident(lset, :foo, :label) == 0

@test_throws Any set_subpart!(lset, 1, :label, :bar)

# @acset macro
#-------------

@present TheoryDecGraph(FreeSchema) begin
  E::Ob
  V::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)

  X::AttrType
  dec::Attr(E,X)
end

@acset_type DecGraph(TheoryDecGraph, index=[:src,:tgt])

g = @acset DecGraph{String} begin
  V = 4
  E = 4
  src = [1,2,3,4]
  tgt = [2,3,4,1]
  dec = ["a","b","c","d"]
end
@test nparts(g, :V) == 4
@test subpart(g, :, :src) == [1,2,3,4]
@test incident(g, 1, :src) == [1]

function path_graph(n::Int)
  @acset DecGraph{Float64} begin
    V = n
    E = n-1
    src = 1:n-1
    tgt = 2:n
    dec = zeros(n-1)
  end
end

pg = path_graph(30)
@test (nparts(pg, :V), nparts(pg, :E)) == (30, 29)
@test incident(pg, 1, :src) == [1]

n = 4
pg = @acset DecGraph{Tuple{Int,Int}} begin
  V = n
  E = n-1
  src = 1:n-1
  tgt = 2:n
  dec = zip(1:n-1, 2:n)
end
@test pg[:dec] == [(1,2), (2,3), (3,4)]

# Test mapping
#-------------

f(s::String) = Int(s[1])

h1 = map(g, dec = f)
h2 = map(g, X = f)

@test h1 == h2

@test subpart(h1,:src) == subpart(g,:src)
@test typeof(h1).super.parameters[2] == Tuple{Int}
@test subpart(h1,:dec) == f.(["a","b","c","d"])

@present TheoryLabeledDecGraph <: TheoryDecGraph begin
  label::Attr(V,X)
end

@acset_type LabeledDecGraph(TheoryLabeledDecGraph, index=[:src,:tgt])

g = @acset LabeledDecGraph{String} begin
  V = 4
  E = 4

  src = [1,2,3,4]
  tgt = [2,3,4,1]

  dec = ["a","b","c","d"]
  label = ["w", "x", "y", "z"]
end

h1 = map(g, X = f)
@test subpart(h1,:label) == f.(["w","x","y","z"])

h2 = map(g, dec = f, label = i -> 3)
@test subpart(h2,:dec) == f.(["a","b","c","d"])
@test subpart(h2,:label) == [3,3,3,3]

@test_throws Any map(g, dec = f)

end

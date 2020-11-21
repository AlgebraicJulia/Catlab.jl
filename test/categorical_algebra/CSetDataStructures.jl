module TestCSetDataStructures
using Test

using Catlab: @present, generator
using Catlab.Theories: compose, id
using Catlab.CSetDataStructures

# Discrete dynamical systems
############################

@present TheoryDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

const AbstractDDS = AbstractCSetType(TheoryDDS)
const DDS = CSetType(TheoryDDS, index=[:Φ])
@test DDS <: AbstractDDS
@test DDS <: CSet

dds = DDS()
@test keys(tables(dds)) == (:X,)
@test keys(dds.indices) == (:Φ,)
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
@test startswith(s, "CSet")
@test occursin("X = 1:3", s)
@test occursin("Φ : X → X = ", s)

s = sprint(show, MIME"text/plain"(), dds)
@test startswith(s, "CSet")
@test occursin("X = 1:3", s)
@test occursin("│ X │", s)

s = sprint(show, MIME"text/html"(), dds)
@test startswith(s, "<div class=\"c-set\">")
@test occursin("<table>", s)
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
UnindexedDDS = CSetType(TheoryDDS)
dds = UnindexedDDS()
add_parts!(dds, :X, 4, Φ=[3,3,4,4])
@test isempty(keys(dds.indices))
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
  R::Data
  parent::Hom(X,X)
  height::Attr(X,R)
end

const AbstractDendrogram = AbstractACSetType(TheoryDendrogram)
const Dendrogram = ACSetType(TheoryDendrogram, index=[:parent])
@test Dendrogram <: AbstractDendrogram
@test Dendrogram <: ACSet
@test Dendrogram{Real} <: AbstractDendrogram{Real}
@test_throws ErrorException CSetType(TheoryDendrogram)

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
@test startswith(s, "ACSet")
@test occursin("R = Int64", s)
@test occursin("height : X → R = ", s)

s = sprint(show, MIME"text/plain"(), d)
@test startswith(s, "ACSet")

# Allow type inheritance for data attributes.
d_abs = Dendrogram{Number}()
add_parts!(d_abs, :X, 2, height=[10.0, 4])
@test subpart(d_abs, :height) == [10.0, 4]

# Dendrograms with leaves
#------------------------

@present TheoryLDendrogram <: TheoryDendrogram begin
  L::Ob
  leafparent::Hom(L,X)
end

const LDendrogram = ACSetType(TheoryLDendrogram, index=[:parent, :leafparent])

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

# Labeled sets
##############

# The simplest example of a C-set with a data attribute, to test data indexing.

@present TheoryLabeledSet(FreeSchema) begin
  X::Ob
  Label::Data
  label::Attr(X,Label)
end

# Labeled sets with index
#------------------------

const IndexedLabeledSet = ACSetType(TheoryLabeledSet, index=[:label])

lset = IndexedLabeledSet{Symbol}()
@test keys(lset.indices) == (:label,)
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
@test occursin("#undef", sprint(show, lset))
@test occursin("#undef", sprint(show, MIME"text/plain"(), lset))
@test occursin("#undef", sprint(show, MIME"text/html"(), lset))

# Labeled sets with unique index
#-------------------------------

const UniqueIndexedLabeledSet = ACSetType(TheoryLabeledSet,
                                          unique_index=[:label])

lset = UniqueIndexedLabeledSet{Symbol}()
@test keys(lset.indices) == (:label,)
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == 1
@test incident(lset, [:foo,:bar], :label) == [1,2]
@test incident(lset, :nonkey, :label) == 0

set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, :baz, :label) == 1
@test incident(lset, :foo, :label) == 0

@test_throws ErrorException set_subpart!(lset, 1, :label, :bar)

end

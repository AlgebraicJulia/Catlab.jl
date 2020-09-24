module TestCSets
using Test

using Catlab: @present
using Catlab.CategoricalAlgebra.CSets

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
@test_throws KeyError subpart(dds, 1, :nonsubpart)
@test_throws KeyError set_subpart!(dds, 1, :nonsubpart, 1)

# Pretty printing.
s = sprint(show, dds)
@test occursin("X = 1:3", s)
@test occursin("Φ : X → X = ", s)

s = sprint(show, MIME"text/plain"(), dds)
@test occursin("X table with 3 elements", s)
@test occursin("(Φ = 1,)", s)

# Error handling.
@test_throws AssertionError add_part!(dds, :X, Φ=5)
@test subpart(dds, :Φ) == [1,1,1,0]
@test incident(dds, 4, :Φ) == []

# Dendrograms
#############

# Strictly speaking, this data structure is not a single dendrogram but a forest
# of dendrograms (whose roots are the elements fixed under the `parent` map) and
# in order to be valid dendrograms, the `height` map must satisfy
# `compose(parent, height) ≥ height` pointwise.

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

d = Dendrogram{Int}()
add_parts!(d, :X, 3, height=0)
add_parts!(d, :X, 2, height=[10,20])
set_subpart!(d, 1:3, :parent, 4)
set_subpart!(d, [4,5], :parent, 5)

@test nparts(d, :X) == 5
@test subpart(d, [1,2,3], :parent) == [4,4,4]
@test subpart(d, 4, :parent) == 5
@test subpart(d, :, :parent) == [4,4,4,5,5]
@test incident(d, 4, :parent) == [1,2,3]
@test has_subpart(d, :height)
@test subpart(d, [1,2,3], :height) == [0,0,0]
@test subpart(d, 4, :height) == 10
@test subpart(d, :, :height) == [0,0,0,10,20]

d2 = Dendrogram{Int}()
copy_parts!(d2, d, :X, [4,5])
@test nparts(d2, :X) == 2
@test subpart(d2, [1,2], :parent) == [2,2]
@test subpart(d2, [1,2], :height) == [10,20]

du = disjoint_union(d, d2)
@test nparts(du, :X) == 7
@test subpart(du, :parent) == [4,4,4,5,5,7,7]
@test subpart(du, :height) == [0,0,0,10,20,10,20]

# Pretty printing of data attributes.
s = sprint(show, d)
@test occursin("R = Int64", s)
@test occursin("height : X → R = ", s)

s = sprint(show, MIME"text/plain"(), d)
@test occursin("(parent = 4, height = 0)", s)

# Allow type inheritance for data attributes.
d = Dendrogram{Number}()
add_parts!(d, :X, 2, parent=[0,0], height=[10.0, 4])
@test subpart(d, :height) == [10.0, 4]

# Labeled sets
##############

# The simplest example of a C-set with a data attribute, to test data indexing.

@present TheoryLabeledSet(FreeSchema) begin
  X::Ob
  Label::Data
  label::Attr(X,Label)
end

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

const UniqueIndexedLabeledSet = ACSetType(TheoryLabeledSet,
                                          unique_index=[:label])

lset = UniqueIndexedLabeledSet{Symbol}()
@test keys(lset.indices) == (:label,)
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == 1
@test incident(lset, [:foo,:bar], :label) == [1,2]
@test incident(lset, :nonkey, :label) == nothing

set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, :baz, :label) == 1
@test incident(lset, :foo, :label) == nothing

@test_throws ErrorException set_subpart!(lset, 1, :label, :bar)

end

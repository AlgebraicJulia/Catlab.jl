module TestCSets
using Test

using Catlab: @present
using Catlab.Theories: FreeCategory
using Catlab.CategoricalAlgebra.CSets

# Discrete dynamical systems
############################

@present TheoryDDS(FreeCategory) begin
  X::Ob
  Φ::Hom(X,X)
end

const AbstractDDS = AbstractCSetType(TheoryDDS)
const DDS = CSetType(TheoryDDS, index=[:Φ])
@test AbstractDDS == AbstractCSet{(:X,),(:Φ,),(1,),(1,)}
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

# Error handling
@test_throws AssertionError add_part!(dds, :X, Φ=5)
@test subpart(dds, :Φ) == [1,1,1,0]
@test incident(dds, 4, :Φ) == []

# Dendrograms
#############

# Strictly speaking, this data structure is not a single dendrogram but a forest
# of dendrograms (whose roots are the elements fixed under the `parent` map) and
# in order to be valid dendrograms, the `height` map must satisfy
# `compose(parent, height) ≥ height` pointwise.

@present TheoryDendrogram(FreeCategory) begin
  X::Ob
  R::Ob
  parent::Hom(X,X)
  height::Hom(X,R)
end

const AbstractDendrogram = AbstractCSetType(TheoryDendrogram, data=[:R])
const Dendrogram = CSetType(TheoryDendrogram, data=[:R], index=[:parent])
@test AbstractDendrogram ==
  AbstractCSet{(:X,),(:parent,),(1,),(1,),(:height,),(1,)}

d = Dendrogram(height=Float64)
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

d2 = empty(d)
copy_parts!(d2, d, :X, [4,5])
@test nparts(d2, :X) == 2
@test subpart(d2, [1,2], :parent) == [2,2]
@test subpart(d2, [1,2], :height) == [10,20]

# Labeled sets
##############

# The simplest example of a C-set with a data attribute, to test data indexing.

@present TheoryLabeledSet(FreeCategory) begin
  X::Ob
  Label::Ob
  label::Hom(X,Label)
end

const IndexedLabeledSet = CSetType(
  TheoryLabeledSet, data=[:Label], index=[:label])

lset = IndexedLabeledSet(label=Symbol)
@test keys(lset.data_indices) == (:label,)
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == [1]
@test isempty(incident(lset, :nonkey, :label))

add_part!(lset, :X, label=:foo)
@test incident(lset, :foo, :label) == [1,3]
set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, [:foo,:baz], :label) == [[3],[1]]

const UniqueIndexedLabeledSet = CSetType(
  TheoryLabeledSet, data=[:Label], unique_index=[:label])

lset = UniqueIndexedLabeledSet(label=Symbol)
@test keys(lset.data_indices) == (:label,)
add_parts!(lset, :X, 2, label=[:foo, :bar])
@test subpart(lset, :, :label) == [:foo, :bar]
@test incident(lset, :foo, :label) == 1
@test incident(lset, [:foo,:bar], :label) == [1,2]
@test incident(lset, :nonkey, :label) == nothing

set_subpart!(lset, 1, :label, :baz)
@test subpart(lset, 1, :label) == :baz
@test incident(lset, :baz, :label) == 1
@test_throws ErrorException set_subpart!(lset, 1, :label, :bar)

end

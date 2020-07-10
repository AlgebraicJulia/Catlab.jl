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
@test AbstractDDS <: AbstractCSet
@test DDS <: AbstractDDS
@test DDS <: CSet

dds = DDS()
@test keys(dds.incident) == (:Φ,)
@test nparts(dds, :X) == 0
@test add_part!(dds, :X) == 1
@test nparts(dds, :X) == 1
@test incident(dds, 1, :Φ) == []

set_subpart!(dds, 1, :Φ, 1)
@test subpart(dds, 1, :Φ) == 1
@test incident(dds, 1, :Φ) == [1]

@test add_part!(dds, :X, (Φ=1,)) == 2
@test add_part!(dds, :X, (Φ=1,)) == 3
@test subpart(dds, [2,3], :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2,3]

@test_throws KeyError subpart(dds, 1, :badname)
@test_throws KeyError set_subpart!(dds, 1, :badname, 1)
@test get_subpart(dds, 1, :Φ, nothing) == 1
@test get_subpart(dds, 1, :badname, nothing) == nothing
@test get_subpart(() -> nothing, dds, 1, :badname) == nothing

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

const Dendrogram = CSetType(TheoryDendrogram, data=[:R], index=[:parent])

d = Dendrogram(height=Float64)
add_parts!(d, :X, 3, (height=0,))
add_parts!(d, :X, 2, (height=[1,2],))
for v in 1:3; set_subpart!(d, v, :parent, 4) end
set_subpart!(d, [4,5], :parent, 5)

@test nparts(d, :X) == 5
@test subpart(d, [1,2,3], :parent) == [4,4,4]
@test subpart(d, 4, :parent) == 5
@test subpart(d, :, :parent) == [4,4,4,5,5]
@test incident(d, 4, :parent) == [1,2,3]
@test subpart(d, [1,2,3], :height)::Vector{Float64} == [0,0,0]
@test subpart(d, 4, :height)::Float64 == 1
@test subpart(d, :, :height) == [0,0,0,1,2]

end

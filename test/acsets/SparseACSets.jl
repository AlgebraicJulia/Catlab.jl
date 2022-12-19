module TestSparseACSets

using Test

using Catlab.SparseACSets
using Tables

# Discrete dynamical systems
############################

SchDDS = BasicSchema([:X], [(:Φ,:X,:X)])

@abstract_acset_type AbstractDDS
@acset_type DDS(SchDDS, index=[:Φ]) <: AbstractDDS
@acset_type UnindexedDDS(SchDDS)
@test DDS <: AbstractDDS
@test DDS <: StructACSet
@test DDS <: StructCSet
@test DDS <: ACSet

dds_makers = [
  DDS,
  UnindexedDDS
]

for dds_maker in dds_makers
  dds = dds_maker()
end

end

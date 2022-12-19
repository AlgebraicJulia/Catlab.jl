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

  @test nparts(dds, :X) == 0
  @test add_part!(dds, :X) == 1
  @test nparts(dds, :X) == 1
  @test incident(dds, 1, :Φ) == Int[]

  set_subpart!(dds, 1, :Φ, 1)
  @test subpart(dds, 1, :Φ) == 1
  @test incident(dds, 1, :Φ) == [1]

  @test add_part!(dds, :X, Φ=1) == 2
  @test add_part!(dds, :X, Φ=1) == 3
  @test subpart(dds, :Φ) == [1,1,1]
  @test subpart(dds, [2,3], :Φ) == [1,1]
  @test incident(dds, 1, :Φ) == [1,2,3]

  # @test has_part(dds, :X)
  # @test !has_part(dds, :nonpart)
  # @test has_part(dds, :X, 3)
  # @test !has_part(dds, :X, 4)
  # @test has_part(dds, :X, 1:5) == [true, true, true, false, false]

  rem_part!(dds, :X, 1)

  @test nparts(dds, :X) == 2
  @test subpart(dds, :Φ) == [0,0,0]
end

end

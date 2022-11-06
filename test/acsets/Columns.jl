module TestColumns
using Test
using Base: OneTo

using DataStructures: OrderedDict
using Catlab.Columns, Catlab.ColumnImplementations
using Catlab.ColumnImplementations: PartialVecMap, PartialDictMap,
  SentinelVecMap, FilledVecMap, DefaultDictMap, DefaultVal, 
  DenseIndexedFinColumn, SparseIndexedFinColumn, DenseFinColumn,
  SparseIndexedFinColumn, SparseFinColumn, TrivialCache

"""
Testing columns is tricky because there is such a wide range of acceptable behavior,
so writing generic tests is not necessarily going to work. So this is going to be a
big file.

What we need to test for mappings:
  - [`Base.getindex`](@ref)
  - [`Base.setindex!`](@ref)
  - [`Base.view`](@ref)
  - [`Base.copy`](@ref)
  - [`Base.map`](@ref)
  - [`isdefined`](@ref)
  - [`undefine_or_clear!`](@ref)
  - [`isdefinable`](@ref)
  - [`set_definable!`](@ref)
  - [`isstored`](@ref)
  - [`store!`](@ref)

The mappings we need to test:
PartialVecMap, PartialDictMap, FilledVecMap, SentinelVecMap, DefaultDictMap

What we need to test for preimagecaches:
  - [`preimage`](@ref)
  - [`add_mapping!`](@ref)
  - [`remove_mapping!`](@ref)
  - [`store!`](@ref)
  - [`maybe_unstore!`](@ref)
  - [`set_definable!`](@ref)

The preimagecaches that we need to test:
TrivialCache, StoredPreimageCache, InjectiveCache
"""

mapping_types = [
  PartialVecMap{Int,Vector{Int}},
  PartialDictMap{Int,Int, Dict{Int,Int}},
  FilledVecMap{Int, DefaultVal{Int, 0}, Vector{Int}},
  SentinelVecMap{Int, DefaultVal{Int, 0}, Vector{Int}},
  DefaultDictMap{Int, Int, DefaultVal{Int, 0}, Dict{Int,Int}}
]

# Basic operations
for mty in mapping_types
  m = mty()
  set_definable!(m, Base.OneTo(6))
  m[3] = 8
  @test m[3] == 8
  m[6] = 1
  @test m[6] == 1
  @test isdefinable(m, 5)
  @test isstored(m, 3)
  @test hash(m) == hash(copy(m))
  @test m == copy(m)

  if mty <: Union{PartialMapping, SentinelVecMap}
    @test !Columns.isdefined(m, 2)
  end
  if mty <: Union{FilledVecMap,DefaultDictMap}
    @test Columns.isdefined(m, 2)
  end

  pvm = mty(OneTo(3), x -> x*2)
  @test pvm[2] == 4
  
end

coltypes = [
  DenseFinColumn{Vector{Int}},
  DenseIndexedFinColumn{Vector{Int}},
  SparseFinColumn{Int,Dict{Int,Int}},
  SparseIndexedFinColumn{Int,Dict{Int,Int}},
  SparseIndexedFinColumn{Int,OrderedDict{Int,Int}},
]

for coltype in coltypes
  col = coltype(OneTo(3), OneTo(6), x -> x*2)
  @test col[1] == 2
  @test Columns.isdefined(col, 3)
  @test isempty(preimage(OneTo(3), col, 1))
  if coltype <: SparseFinColumn || coltype <: SparseIndexedFinColumn
    @test_skip preimage(OneTo(3), col, 2) == [1]
  else 
    @test preimage(OneTo(3), col, 2) == [1]
  end
end

dfc = DenseFinColumn{UnitRange{Int}}(
  SentinelVecMap{Int, DefaultVal{Int, 0}, UnitRange{Int}}(2:5), 
  TrivialCache{Int, Int}())

@test dfc[3] == 4 
@test preimage(OneTo(3), dfc, 2) == [1]

end # module

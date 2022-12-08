module TestMappings

using Test
using Catlab.Columns, Catlab.Mappings

# VecMap-specific tests

v = VecMap([:A, :B, :C])
@test v[1] == :A

# General tests

testvals = Dict(1 => :a, 4 => :b, 200 => :c)

mappingtypes = [
  VecMap{Symbol},
  DictMap{Int,Symbol}
]

for M in mappingtypes
  m = M()
  sizehint!(m, 200)
  for (k, v) in testvals
    m[k] = v
  end
  for (k, v) in testvals
    @test haskey(m, k)
    @test m[k] == v
  end
  @test length(m) == 3
  @test sort(collect(keys(m))) == [1,4,200]
  delete!(m, 4)
  @test sort(collect(keys(m))) == [1,200]
  @test_throws Exception m[4]
  m′ = copy(m)
  @test m′ == m

  @test :b == get!(m, 4, :b)
  m′ = M(testvals...)
  @test m′ == m
end

# MappingView

v = VecMap(testvals...)
mv = view(v, 4:200)

@test mv[1] == :b
@test length(mv) == 197

mvv = view(mv, 197:197)

@test mvv[1] == :c

end

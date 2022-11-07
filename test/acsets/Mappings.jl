module TestMappings

using Test
using Catlab.Columns, Catlab.Mappings

testvals = Dict(1 => :a, 4 => :b, 200 => :c)

mappingtypes = [
  VecMap{Symbol},
  DictMap{Int,Symbol}
]

for M in mappingtypes
  m = M()
  for (k, v) in testvals
    m[k] = v
  end
  for (k, v) in testvals
    @test haskey(m, k)
    @test m[k] == v
  end
  @test sort(collect(keys(m))) == [1,4,200]
  delete!(m, 4)
  @test sort(collect(keys(m))) == [1,200]
  m′ = copy(m)
  @test m′ == m
end

end

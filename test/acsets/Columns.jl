module TestColumns
using Test
using Base: OneTo
using DataStructures: OrderedDict

using Catlab.Columns, Catlab.ColumnImplementations

# Columns
#########

# Int → Int columns
#------------------

coltypes = [
  column_type(subpart_type, NoIndex, sparsity)
  for subpart_type in [HomChoice, AttrChoice(Int)]
    for sparsity in [Dense, Sparse(Int)]
      for index_type in [NoIndex, Index, UniqueIndex]
]

for coltype in coltypes
  col = coltype(1 => 2, 2 => 4, 3 => 6)
  @test col[1] == 2
  @test haskey(col, 3)
  @test isempty(preimage(OneTo(3), col, 1))
  @test collect(preimage(OneTo(3), col, 2)) == [1]
end

# Int → Symbol columns
#---------------------

coltypes = [
  column_type(AttrChoice(Symbol), index_type, sparsity)
  for sparsity in [Dense, Sparse(Int)]
    for index_type in [NoIndex, Index, UniqueIndex]
]

for coltype in coltypes
  col = coltype(1=>:A,2=>:B,3=>:C)
  @test col[1] == :A
  @test haskey(col, 3)
  @test isempty(preimage(OneTo(3), col, :F))
  @test collect(preimage(OneTo(3), col, :A)) == [1]
end

end # module

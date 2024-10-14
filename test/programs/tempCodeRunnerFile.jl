module TestRelationalPrograms

using Test

using Catlab.CategoricalAlgebra.CSets
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.Programs.RelationalPrograms

# Relation macro
################

# Untyped
#--------

parsed = @relation (x,z) where (x,y,z) begin
  R(x,y)
  S(y,z)
end
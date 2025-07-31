module TestMADCSetHomSearch

using Catlab, Test

# Graphs 
#########


@acset_type MADGraph(SchGraph, part_type=BitSetParts) <: AbstractGraph

Grph = ACSetCategory(MADCSetCat(MADGraph()))

v1, v2 = MADGraph.(1:2)
@test !is_isomorphic(v1, v2; cat=Grph)
rem_part!(v2, :V, 1)
@test is_isomorphic(v1, v2; cat=Grph)

σ = isomorphism(v2, v1; cat=Grph)
@test is_natural(σ; cat=Grph)

end # module

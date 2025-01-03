module TestMADCSetHomSearch

@acset_type AbsMADGraph(SchWeightedGraph, part_type=BitSetParts) <: AbstractGraph
const MADGraph = AbsMADGraph{Symbol}

v1, v2 = MADGraph.(1:2)
@test !is_isomorphic(v1, v2)
rem_part!(v2, :V, 1)
@test is_isomorphic(v1, v2)
@test is_isomorphic(v2, v1)


end # module

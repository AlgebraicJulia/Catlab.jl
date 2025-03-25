module TestMadHomSearch

using Catlab, Test

@acset_type AbsMADGraph(SchWeightedGraph, part_type=BitSetParts) <: AbstractGraph
const MADGraph = AbsMADGraph{Symbol}
p2, p3 = path_graph.(MADGraph, 3:4)
p2[:weight] = [:y,AttrVar(add_part!(p2, :Weight))]
p3[:weight] = [AttrVar(add_part!(p3, :Weight)), :y, AttrVar(add_part!(p3, :Weight))]
f = homomorphism(p2, p3)
@test in_bounds(f) && is_natural(f)
rem_part!(p3, :Weight, 2)
p3[3, :weight] = :z
@test !in_bounds(f) 

f = homomorphism(p2, p3)
@test in_bounds(f) && is_natural(f)
rem_part!(p3, :E, 3)
rem_part!(p3, :V, 4)
@test !in_bounds(f)



@acset_type AbsMADGraph(SchWeightedGraph, part_type=BitSetParts) <: AbstractGraph
const MADGraph = AbsMADGraph{Symbol}

v1, v2 = MADGraph.(1:2)
@test !is_isomorphic(v1, v2)
rem_part!(v2, :V, 1)
@test is_isomorphic(v1, v2)
@test is_isomorphic(v2, v1)

end # module

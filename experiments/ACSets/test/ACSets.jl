using ACSets
using StructArrays

g = DecGraph{Symbol}()

@test add_parts!(g,:V,StructArray(vdec=[:a,:b,:d])) == 1:3

@test subpart(g,:vdec) == [:a,:b,:d]

@test subpart(g,2,:vdec) == :b

@test incident(g,:a,:vdec) == [1]

@test add_parts!(g,:E,StructArray(src=[1,2],tgt=[2,3],edec=[:f,:g])) == 1:2

@test incident(g,3,:tgt) == [2]

set_subpart!(g,2,:tgt,2)

@test incident(g,3,:tgt) == []

@test incident(g,2,:tgt) == [1,2]

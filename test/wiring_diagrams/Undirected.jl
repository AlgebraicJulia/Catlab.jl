module TestUndirectedWiringDiagrams
using Test

using Catlab.WiringDiagrams.UndirectedWiringDiagrams

# Imperative interface
######################

# Untyped wiring diagrams.
d = UndirectedWiringDiagram(3)
@test nboxes(d) == 0
@test njunctions(d) == 0
add_box!(d, 2); add_box!(d, 2); add_box!(d, 2)
add_junctions!(d, 4)
@test box(d, 1) == 1
@test box(d, 1:4) == [1,1,2,2]
@test nboxes(d) == 3
@test njunctions(d) == 4
@test collect(boxes(d)) == collect(1:3)
@test collect(junctions(d)) == collect(1:4)
@test collect(ports(d)) == collect(1:6)
@test collect(ports(d, outer=true)) == collect(1:3)
@test ports(d, outer_box(d)) == [1,2,3]
@test ports.([d], boxes(d)) == [[1,2], [3,4], [5,6]]
set_junction!(d, [1,3,5], 1:3)
set_junction!(d, [2,4,6], 4)
set_junction!(d, 1:3, 1:3, outer=true)
@test junction(d, 1) == 1
@test junction(d, 1, outer=true) == 1
@test junction(d, [2,4,6]) == [4,4,4]
@test ports_with_junction(d, 1) == [1]
@test ports_with_junction(d, 1, outer=true) == [1]
@test ports_with_junction(d, 4) == [2,4,6]

# Typed wiring diagrams.
d = UndirectedWiringDiagram([:X,:Y,:Z])
add_box!(d, [:X,:W]); add_box!(d, [:Y,:W]); add_box!(d, [:Z,:W])
add_junctions!(d, [:X,:Y,:Z,:W])
@test port_type(d, 1) == :X
@test port_type(d, [1,3,5]) == [:X,:Y,:Z]
@test port_type(d, 3, outer=true) == :Z
@test junction_type(d, 3) == :Z
set_junction!(d, [1,3,5], 1:3)
set_junction!(d, [2,4,6], 4)
set_junction!(d, 1:3, 1:3, outer=true)
@test junction(d, 1:6) == [1,4,2,4,3,4]
@test junction(d, 1:3, outer=true) == [1,2,3]
@test_throws ErrorException set_junction!(d, 1, 2)

# Interface for ports that is relative to their boxes.
d_previous = d
d = UndirectedWiringDiagram([:X,:Y,:Z])
add_box!(d, [:X,:W]); add_box!(d, [:Y,:W]); add_box!(d, [:Z,:W])
@test port_type(d, (1,1)) == :X
@test port_type(d, (2,1)) == :Y
add_wires!(d, (i,1) => (outer_box(d),i) for i in 1:3)
add_wire!(d, (1,2) => (2,2))
add_wire!(d, (2,2) => (3,2))
@test d == d_previous

# Operadic interface
####################

f = UndirectedWiringDiagram(3)
add_box!(f, 2); add_box!(f, 2); add_box!(f, 2)
add_junctions!(f, 4)
set_junction!(f, [1,4,2,4,3,4])
set_junction!(f, 1:3, outer=true)

g1 = UndirectedWiringDiagram(2)
add_box!(g1, 1); add_box!(g1, 1)
add_junctions!(g1, 2)
set_junction!(g1, 1:2)
set_junction!(g1, 1:2, outer=true)
g2 = copy(g1)
set_junction!(g2, 2:-1:1)

h = UndirectedWiringDiagram(3)
add_box!(h, 2); add_box!(h, 1); add_box!(h, 1); add_box!(h, 2)
add_junctions!(h, 4)
set_junction!(h, [1,4,4,2,3,4])
set_junction!(h, 1:3, outer=true)
@test ocompose(f,2,g2) == h
@test ocompose(ocompose(f,1,g1),3,g2) == ocompose(ocompose(f,2,g2),1,g1)

h = UndirectedWiringDiagram(3)
for i in 1:6; add_box!(h, 1) end
add_junctions!(h, 4)
set_junction!(h, [1,4,4,2,3,4])
set_junction!(h, 1:3, outer=true)
@test ocompose(f, [g1,g2,g1]) == h

end

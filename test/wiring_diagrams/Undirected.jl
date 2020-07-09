module TestUndirectedWiringDiagrams
using Test

using Catlab.WiringDiagrams.UndirectedWiringDiagrams

# Imperative interface
######################

# Untyped wiring diagrams.
d = UndirectedWiringDiagram(3)
@test nboxes(d) == 0
@test nlinks(d) == 0
add_box!(d, 2); add_box!(d, 2); add_box!(d, 2)
add_links!(d, 4)
@test box(d, 1) == 1
@test box(d, 1:4) == [1,1,2,2]
@test nboxes(d) == 3
@test nlinks(d) == 4
@test collect(boxes(d)) == collect(1:3)
@test collect(links(d)) == collect(1:4)
@test collect(ports(d)) == collect(1:6)
@test collect(ports(d, outer=true)) == collect(1:3)
@test ports(d, outer_box(d)) == [1,2,3]
@test ports.([d], boxes(d)) == [[1,2], [3,4], [5,6]]
set_link!(d, [1,3,5], 1:3)
set_link!(d, [2,4,6], 4)
set_link!(d, 1:3, 1:3, outer=true)
@test link(d, 1) == 1
@test link(d, 1, outer=true) == 1
@test link(d, [2,4,6]) == [4,4,4]
@test linked_ports(d, 1) == [1]
@test linked_ports(d, 1, outer=true) == [1]
@test linked_ports(d, 4) == [2,4,6]

# Typed wiring diagrams.
# TODO: Enforce type compatibility.
d = UndirectedWiringDiagram([:X,:Y,:Z])
add_box!(d, [:X,:W]); add_box!(d, [:Y,:W]); add_box!(d, [:Z,:W])
add_links!(d, [:X,:Y,:Z,:W])
set_link!(d, [1,3,5], 1:3)
set_link!(d, [2,4,6], 4)
set_link!(d, 1:3, 1:3, outer=true)
@test link(d, 1:6) == [1,4,2,4,3,4]
@test link(d, 1:3, outer=true) == [1,2,3]

end

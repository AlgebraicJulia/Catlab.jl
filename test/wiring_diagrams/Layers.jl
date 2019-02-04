module TestWiringLayers

using Test
using Catlab.Doctrines, Catlab.WiringDiagrams

# Low-level graph interface
###########################

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)

f = WiringLayer([A, B, C], [C, B, A])
@test input_ports(f) == [A, B, C]
@test output_ports(f) == [C, B, A]
@test nwires(f) == 0
@test wires(f) == []

add_wire!(f, 1 => 3)
@test has_wire(f, 1 => 3)
@test !has_wire(f, 3 => 1)
@test_throws BoundsError add_wire!(f, 4 => 1) # Source out of bounds
@test_throws BoundsError add_wire!(f, 1 => 4) # Target out of bounds

add_wires!(f, [2 => 2, 3 => 1])
@test nwires(f) == 3
@test sort!(wires(f)) == [1 => 3, 2 => 2, 3 => 1]

@test nwires(f, 1 => 3) == 1
add_wires!(f, [1 => 3, 1 => 3])
@test nwires(f, 1 => 3) == 3
@test sort!(wires(f)) == [1 => 3, 1 => 3, 1 => 3, 2 => 2, 3 => 1]
rem_wire!(f, 1 => 3)
@test nwires(f, 1 => 3) == 2
rem_wires!(f, 1 => 3)
@test !has_wire(f, f => 3)
@test nwires(f, 1 => 3) == 0

end

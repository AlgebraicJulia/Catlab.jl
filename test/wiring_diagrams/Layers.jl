module TestWiringLayers

using Test
using Catlab.Doctrines, Catlab.WiringDiagrams

# Low-level graph interface
###########################

a, b, c = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)

f = WiringLayer([a, b, c], [c, b, a])
@test input_ports(f) == [a, b, c]
@test output_ports(f) == [c, b, a]
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
@test out_wires(f, 1) == [1 => 3, 1 => 3, 1 => 3]
rem_wire!(f, 1 => 3)
@test nwires(f, 1 => 3) == 2
rem_wires!(f, 1 => 3)
@test !has_wire(f, f => 3)
@test nwires(f, 1 => 3) == 0
@test sort!(wires(f)) == [2 => 2, 3 => 1]

# High-level categorical interface
##################################

A, B, C = Layer([a]), Layer([b]), Layer([c])

# Category
@test compose(id(A), id(A)) == id(A)

# Symmetric monoidal category
@test otimes(id(A), id(B)) == id(otimes(A,B))
@test compose(braid(A,B), braid(B,A)) == id(otimes(A,B))

# Diagonals
@test compose(otimes(mcopy(A), mcopy(B)), otimes(id(A), braid(A,B), id(B))) ==
  mcopy(otimes(A,B))
@test compose(mcopy(A), otimes(mcopy(A), id(A))) == mcopy(A, 3)
@test compose(mcopy(A), otimes(id(A), mcopy(A))) == mcopy(A, 3)
@test compose(mcopy(A), otimes(id(A), delete(A))) == id(A)

# Codiagonals
@test compose(otimes(id(A), braid(B,A), id(B)), otimes(mmerge(A), mmerge(B))) ==
  mmerge(otimes(A,B))
@test compose(otimes(mmerge(A), id(A)), mmerge(A)) == mmerge(A, 3)
@test compose(otimes(id(A), mmerge(A)), mmerge(A)) == mmerge(A, 3)
@test compose(otimes(id(A), create(A)), mmerge(A)) == id(A)

end

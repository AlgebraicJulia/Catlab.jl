module TestWiringLayers

using Test
using Catlab.WiringDiagrams

# Low-level graph interface
###########################

f = WiringLayer(3, 3)
@test nwires(f) == 0
@test wires(f) == []

add_wire!(f, 1 => 3)
@test has_wire(f, 1 => 3)
@test !has_wire(f, 3 => 1)
@test_throws BoundsError add_wire!(f, 4 => 1) # Source out of bounds
@test_throws BoundsError add_wire!(f, 1 => 4) # Target out of bounds

add_wires!(f, [2 => 2, 3 => 1])
@test nwires(f) == 3
@test wires(f) == [1 => 3, 2 => 2, 3 => 1]

@test nwires(f, 1 => 3) == 1
add_wires!(f, [1 => 3, 1 => 3])
@test nwires(f, 1 => 3) == 3
@test wires(f) == [1 => 3, 1 => 3, 1 => 3, 2 => 2, 3 => 1]
@test out_wires(f, 1) == [1 => 3, 1 => 3, 1 => 3]
rem_wire!(f, 1 => 3)
@test nwires(f, 1 => 3) == 2
rem_wires!(f, 1 => 3)
@test !has_wire(f, 1 => 3)
@test nwires(f, 1 => 3) == 0
@test wires(f) == [2 => 2, 3 => 1]

# High-level categorical interface
##################################

A, B, C = NLayer(1), NLayer(1), NLayer(1)

# Category
@test id(A) == complete_layer(1,1)
@test compose(id(A), id(A)) == id(A)

# Symmetric monoidal category
@test otimes(id(A), id(B)) == id(otimes(A,B))
@test compose(braid(A,B), braid(B,A)) == id(otimes(A,B))

# Diagonals
@test mcopy(A) == complete_layer(1,2)
@test delete(A) == complete_layer(1,0)
@test compose(otimes(mcopy(A), mcopy(B)), otimes(id(A), braid(A,B), id(B))) ==
  mcopy(otimes(A,B))
@test compose(mcopy(A), otimes(mcopy(A), id(A))) == mcopy(A, 3)
@test compose(mcopy(A), otimes(id(A), mcopy(A))) == mcopy(A, 3)
@test compose(mcopy(A), otimes(id(A), delete(A))) == id(A)

# Codiagonals
@test mmerge(A) == complete_layer(2,1)
@test create(A) == complete_layer(0,1)
@test compose(otimes(id(A), braid(B,A), id(B)), otimes(mmerge(A), mmerge(B))) ==
  mmerge(otimes(A,B))
@test compose(otimes(mmerge(A), id(A)), mmerge(A)) == mmerge(A, 3)
@test compose(otimes(id(A), mmerge(A)), mmerge(A)) == mmerge(A, 3)
@test compose(otimes(id(A), create(A)), mmerge(A)) == id(A)

# Wiring diagrams
#################

function roundtrip(layer::WiringLayer)::WiringLayer
  ports = n::Int -> repeat([nothing], n)
  diagram = to_wiring_diagram(layer, ports(layer.ninputs), ports(layer.noutputs))
  wiring_layer_between(diagram, input_id(diagram), output_id(diagram))
end

layer = WiringLayer(3, 3)
add_wires!(layer, [1 => 1, 1 => 2, 2 => 3, 3 => 1, 3 => 3])
@test roundtrip(layer) == layer

end

module TestWiringDiagramCore
using Test

using Catlab.WiringDiagrams.WiringDiagramCore
import Catlab.WiringDiagrams.WiringDiagramCore: validate_ports

# For testing purposes, check equality of port symbols.
function validate_ports(source_port::Symbol, target_port::Symbol)
  if source_port != target_port
    error("Source port $source_port does not equal target port $target_port")
  end
end

A, B, C, D = [:A], [:B], [:C], [:D]
f = Box(:f, A, B)
g = Box(:g, B, C)
h = Box(:h, C, D)

# Imperative interface
######################

# Operations on boxes
d = WiringDiagram(A, C)
@test nboxes(d) == 0
@test_throws KeyError box(d,input_id(d))
@test_throws KeyError box(d,output_id(d))

fv = add_box!(d, f)
@test nboxes(d) == 1
@test box(d, fv).value == :f
@test box(d, fv) == f
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, f)
gv = add_box!(d, g)
hv = add_box!(d, h)
@test nboxes(d) == 3
@test [b.value for b in boxes(d)] == [:f,:g,:h]
@test boxes(d) == [f,g,h]
rem_boxes!(d, [fv,hv])
@test nboxes(d) == 1
@test boxes(d) == [g]

# Operations on ports
d = WiringDiagram(A, C)
fv = add_box!(d, f)
gv = add_box!(d, g)

@test input_ports(d, fv) == A
@test output_ports(d, fv) == B
@test input_ports(d, output_id(d)) == C
@test output_ports(d, input_id(d)) == A
@test_throws ErrorException input_ports(d, input_id(d))
@test_throws ErrorException output_ports(d, output_id(d))

@test port_value(d, Port(input_id(d),OutputPort,1)) == :A
@test port_value(d, Port(output_id(d),InputPort,1)) == :C
@test port_value(d, Port(fv,InputPort,1)) == :A
@test port_value(d, Port(fv,OutputPort,1)) == :B

# Operations on wires
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
@test !has_wire(d, (fv,1) => (gv,1))
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test has_wire(d, (fv,1) => (gv,1))
@test_throws ErrorException add_wire!(d, (gv,1) => (fv,1))
@test wires(d) == map(Wire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])

# Shallow copies.
d_copy = copy(d)
rem_boxes!(d_copy, [fv,gv])
@test nboxes(d) == 2
@test nwires(d) == 3

# Graph properties.
@test Set(all_neighbors(d, fv)) == Set([input_id(d),gv])
@test Set(all_neighbors(d, gv)) == Set([fv,output_id(d)])
@test neighbors(d, fv) == [gv]
@test outneighbors(d, fv) == [gv]
@test inneighbors(d, gv) == [fv]
@test wires(d, input_id(d)) == [ Wire((input_id(d),1) => (fv,1)) ]
@test wires(d, fv) == map(Wire, [
  ((input_id(d),1) => (fv,1)),
  ((fv,1) => (gv,1))
])
@test out_wires(d, fv) == [ Wire((fv,1) => (gv,1)) ]
@test out_wires(d, Port(fv,OutputPort,1)) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, gv) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, Port(gv,InputPort,1)) == [ Wire((fv,1) => (gv,1)) ]

rem_wires!(d, fv, gv)
@test nwires(d) == 2
@test !has_wire(d, fv, gv)
rem_wire!(d, (input_id(d),1) => (fv,1))
@test wires(d) == [ Wire((gv,1) => (output_id(d),1)) ]

# Induced subgraph.
d = WiringDiagram(A,D)
fv, gv, hv = add_box!(d, f), add_box!(d, g), add_box!(d, h)
add_wires!(d, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(d),1),
])
sub = WiringDiagram(A, D)
fv, gv = add_box!(sub, f), add_box!(sub, g)
add_wires!(sub, Pair[
  (input_id(sub),1) => (fv,1),
  (fv,1) => (gv,1),
])
@test induced_subdiagram(d, [fv, gv]) == sub

# Substitution
##############

sub = WiringDiagram(B,D)
gv = add_box!(sub, g)
hv = add_box!(sub, h)
add_wires!(sub, Pair[
  (input_id(sub),1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(sub),1),
])
d0 = WiringDiagram(A,D)
fv = add_box!(d0, f)
subv = add_box!(d0, sub)
add_wires!(d0, Pair[
  (input_id(d0),1) => (fv,1),
  (fv,1) => (subv,1),
  (subv,1) => (output_id(d0),1),
])
@test boxes(d0) == [ f, sub ]
@test boxes(sub) == [ g, h ]
d = substitute(d0, subv)
@test nboxes(d) == 3
@test boxes(d) == [f, g, h]
box_map = Dict(box(d,v).value => v for v in box_ids(d))
@test nwires(d) == 4
@test Set(wires(d)) == Set(map(Wire, [
  (input_id(d),1) => (box_map[:f],1),
  (box_map[:f],1) => (box_map[:g],1),
  (box_map[:g],1) => (box_map[:h],1),
  (box_map[:h],1) => (output_id(d),1),
]))

# Encapsulation
###############

d0 = WiringDiagram(A,D)
fv = add_box!(d0, f)
gv = add_box!(d0, g)
hv = add_box!(d0, h)
add_wires!(d0, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(d),1)
])

d = encapsulate(d0, [fv,gv])
@test nboxes(d) == 2
@test sum(isa(b, WiringDiagram) for b in boxes(d)) == 1
@test nwires(d) == 3
sub = first(b for b in boxes(d) if isa(b, WiringDiagram))
@test nboxes(sub) == 2
@test boxes(sub) == [f, g]
box_map = Dict(box(sub,v).value => v for v in box_ids(sub))
@test Set(wires(sub)) == Set(map(Wire, [
  (input_id(sub),1) => (box_map[:f],1),
  (box_map[:f],1) => (box_map[:g],1),
  (box_map[:g],1) => (output_id(sub),1),
]))

d = encapsulate(d0, [fv,gv], discard_boxes=true, value=:e)
@test boxes(d) == [ Box(:e, A, C), h ]
box_map = Dict(box(d,v).value => v for v in box_ids(d))
@test Set(wires(d)) == Set(map(Wire, [
  (input_id(d),1) => (box_map[:e],1),
  (box_map[:e],1) => (box_map[:h],1),
  (box_map[:h],1) => (output_id(d),1),
]))

d0 = WiringDiagram(A,B)
v1 = add_box!(d0, f)
v2 = add_box!(d0, f)
add_wires!(d0, Pair[
  (input_id(d),1) => (v1,1),
  (input_id(d),1) => (v2,1),
  (v1,1) => (output_id(d),1),
  (v2,1) => (output_id(d),1),
])
d = encapsulate(d0, [v1,v2])
@test nboxes(d) == 1
@test nwires(d) == 2
sub = first(boxes(d))
@test sub == d0

end

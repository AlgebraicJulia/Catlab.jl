module TestYFilesWiringDiagrams

using Test
using Catlab.WiringDiagrams, Catlab.Graphics

function read_yfiles(name::String; kw...)
  filename = joinpath(@__DIR__, "data", name)
  read_yfiles_diagram(Symbol, Symbol, filename; kw...)
end

ports(n::Int) = repeat([nothing], n)
d = WiringDiagram(ports(1), ports(1))
fv = add_box!(d, Box(:f, ports(1), ports(2)))
gv = add_box!(d, Box(:g, ports(2), ports(1)))
hv = add_box!(d, Box(:h, ports(1), ports(1)))
kv = add_box!(d, Box(:k, ports(1), ports(1)))
add_wires!(d, [
  Wire(:A, (input_id(d),1) => (fv, 1)),
  Wire(:B, (fv,1) => (hv,1)), Wire(:C, (fv,2) => (kv,1)),
  Wire(:D, (hv,1) => (gv,1)), Wire(:E, (kv,1) => (gv,2)),
  Wire(:F, (gv,1) => (output_id(d),1)),
])

d_vertical = read_yfiles("yed_vertical.graphml", direction=:vertical)
@test nboxes(d_vertical) == nboxes(d)
perm = sortperm(boxes(d_vertical); by=box->box.value)
@test is_permuted_equal(d_vertical, d, perm)

d_horizontal = read_yfiles("yed_horizontal.graphml", direction=:horizontal)
@test nboxes(d_horizontal) == nboxes(d)
perm = sortperm(boxes(d_horizontal); by=box->box.value)
@test is_permuted_equal(d_horizontal, d, perm)

end

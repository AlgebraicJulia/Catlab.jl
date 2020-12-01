""" Algebras of operads of wiring diagrams.
"""
module WiringDiagramAlgebras
export oapply

using Compat: isnothing

using ...CategoricalAlgebra
using ..UndirectedWiringDiagrams

""" Compose morphisms according to UWD.

The morphisms corresponding to the boxes, and optionally also the objects
corresponding to the junctions, are given by dictionaries indexed by
box/junction attributes. The default attributes are those compatible with the
`@relation` macro.
"""
function oapply(composite::UndirectedWiringDiagram, hom_map::AbstractDict,
                ob_map::Union{AbstractDict,Nothing}=nothing;
                hom_attr::Symbol=:name, ob_attr::Symbol=:variable)
  homs = [ hom_map[name] for name in subpart(composite, hom_attr) ]
  obs = isnothing(ob_map) ? nothing :
    [ ob_map[name] for name in subpart(composite, ob_attr) ]
  oapply(composite, homs, obs)
end

# Tensors
#########

function oapply(d::UndirectedWiringDiagram,
                tensors::AbstractVector{<:AbstractArray})
  @assert nboxes(d) == length(tensors)
  contract_tensor_network(tensors,
                          [junction(d, ports(d, b)) for b in boxes(d)],
                          junction(d, ports(d, outer=true), outer=true))
end

""" Generalized contraction of two tensors of arbitrary rank.

This function includes matrix multiplication, tensor product, and trace as
special cases. The interface similar to that of the `ncon` ("Network
CONtractor") function in:

- the [NCON package](https://arxiv.org/abs/1402.0939) for MATLAB
- the Julia package [TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl)

except that the outer junctions are represented explictly by a third argument
rather than implicitly by using negative numbers in the second argument.
"""
function contract_tensor_network((A, B), (jA, jB), j_out)
  njunc = maximum(Iterators.flatten((jA, jB, j_out)))
  jA, jB, j_out = Tuple(jA), Tuple(jB), Tuple(j_out)
  jsizes = fill(-1, njunc)
  for (i,j) in enumerate(jA); jsizes[j] = size(A, i) end
  for (i,j) in enumerate(jB); jsizes[j] = size(B, i) end
  jsizes = Tuple(jsizes)

  C = zeros(eltype(A), Tuple(jsizes[j] for j in j_out))
  for index in CartesianIndices(jsizes)
    C[(index[j] for j in j_out)...] +=
      A[(index[j] for j in jA)...] * B[(index[j] for j in jB)...]
  end
  return C
end

# Structured multicospans
#########################

""" Compose structured multicospans according to UWD.

This function makes structured multicospans into an algebra of the operad of
undirected wiring diagrams.
"""
function oapply(composite::UndirectedWiringDiagram,
                cospans::AbstractVector{<:StructuredMulticospan{L}},
                junction_feet::Union{AbstractVector,Nothing}=nothing) where L
  @assert nboxes(composite) == length(cospans)
  if isnothing(junction_feet)
    junction_feet = Vector{first(dom(L))}(undef, njunctions(composite))
  else
    @assert njunctions(composite) == length(junction_feet)
  end

  # Create free diagram whose generating graph is a bipartite graph of the UWD's
  # boxes and junctions. Each directed edge goes from a junction vertex to a box
  # vertex, as defined by the UWD's junction map, and the edge is mapped to the
  # corresponding leg of a multicospan.
  diagram = FreeDiagram{codom(L)...}()
  add_vertices!(diagram, nboxes(composite), ob=map(apex, cospans))
  jmap = add_vertices!(diagram, njunctions(composite))
  for (b, cospan) in zip(boxes(composite), cospans)
    for (p, leg, foot) in zip(ports(composite, b), legs(cospan), feet(cospan))
      j = junction(composite, p)
      add_edge!(diagram, jmap[j], b, hom=leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error(
          "Domains of structured cospans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  set_subparts!(diagram, jmap, ob=map(L, junction_feet))

  # The composite multicospan is given by the colimit of this diagram.
  colim = colimit(diagram)
  outer_js = junction(composite, outer=true)
  outer_legs, outer_feet = legs(colim)[jmap[outer_js]], junction_feet[outer_js]
  StructuredMulticospan{L}(Multicospan(ob(colim), outer_legs), outer_feet)
end

end

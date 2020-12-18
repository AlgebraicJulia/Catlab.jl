""" Algebras of operads of wiring diagrams.
"""
module WiringDiagramAlgebras
export oapply, query

using Compat: isnothing
import TypedTables

using ...Theories, ...CategoricalAlgebra,
  ...CategoricalAlgebra.Sets, ...CategoricalAlgebra.FinSets
using ...CSetDataStructures: make_table
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

# UWD algebras of multi(co)spans
################################

function oapply(composite::UndirectedWiringDiagram,
                spans::AbstractVector{<:Multispan}; Ob=nothing, Hom=nothing)
  @assert nboxes(composite) == length(spans)
  # FIXME: This manual type inference is hacky and bad. The right solution is to
  # extend `Multi(co)span` with type parameters that allow abstract types.
  if isnothing(Ob); Ob = typejoin(mapreduce(typeof∘apex, typejoin, spans),
                                  mapreduce(eltype∘feet, typejoin, spans)) end
  if isnothing(Hom); Hom = mapreduce(eltype∘legs, typejoin, spans) end
  junction_feet = Vector{Ob}(undef, njunctions(composite))

  # Create bipartite free diagram whose vertices of types 1 and 2 are the UWD's
  # boxes and junctions, respectively.
  diagram = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(diagram, nboxes(composite), ob₁=map(apex, spans))
  add_vertices₂!(diagram, njunctions(composite))
  for (b, span) in zip(boxes(composite), spans)
    for (p, leg) in zip(ports(composite, b), legs(span))
      j = junction(composite, p)
      add_edge!(diagram, b, j, hom=leg)
      foot = codom(leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error("Feet of spans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  all(isassigned(junction_feet, j) for j in junctions(composite)) ||
    error("Limits with isolated junctions are not supported")
  diagram[:ob₂] = junction_feet

  # The composite multispan is given by the limit of this diagram.
  lim = limit(diagram)
  outer_legs = map(junction(composite, outer=true)) do j
    e = first(incident(diagram, j, :tgt))
    legs(lim)[src(diagram, e)] ⋅ hom(diagram, e)
  end
  Multispan(ob(lim), outer_legs)
end

function oapply(composite::UndirectedWiringDiagram,
                cospans::AbstractVector{<:StructuredMulticospan{L}},
                junction_feet::Union{AbstractVector,Nothing}=nothing) where L
  @assert nboxes(composite) == length(cospans)
  if isnothing(junction_feet)
    junction_feet = Vector{first(dom(L))}(undef, njunctions(composite))
  else
    @assert njunctions(composite) == length(junction_feet)
  end

  # Create bipartite free diagram whose vertices of types 1 and 2 are the UWD's
  # junctions and boxes, respectively.
  diagram = BipartiteFreeDiagram{codom(L)...}()
  add_vertices₁!(diagram, njunctions(composite))
  add_vertices₂!(diagram, nboxes(composite), ob₂=map(apex, cospans))
  for (b, cospan) in zip(boxes(composite), cospans)
    for (p, leg, foot) in zip(ports(composite, b), legs(cospan), feet(cospan))
      j = junction(composite, p)
      add_edge!(diagram, j, b, hom=leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error("Feet of cospans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  diagram[:ob₁] = map(L, junction_feet)

  # Find, or if necessary create, an outgoing edge for each junction. The
  # existence of such edges is an assumption for colimits of bipartite diagrams.
  # The edges are also needed to construct inclusions for the outer junctions.
  junction_edges = map(junctions(composite)) do j
    out_edges = incident(diagram, j, :src)
    if isempty(out_edges)
      x = ob₁(diagram, j)
      v = add_vertex₂!(diagram, ob₂=x)
      add_edge!(diagram, j, v, hom=id(x))
    else
      first(out_edges)
    end
  end

  # The composite multicospan is given by the colimit of this diagram.
  colim = colimit(diagram)
  outer_js = junction(composite, outer=true)
  outer_legs = map(junction_edges[outer_js]) do e
    hom(diagram, e) ⋅ legs(colim)[tgt(diagram, e)]
  end
  outer_feet = junction_feet[outer_js]
  StructuredMulticospan{L}(Multicospan(ob(colim), outer_legs), outer_feet)
end

# Queries via UWD algebras
##########################

""" Evaluate a conjunctive query on an attributed C-set.

The query is a undirected wiring diagram whose boxes and ports are assumed to be
named through attributes `:name` and `:port_name`/`:outer_port_name`. To define
such a diagram, use the named form of the [`@relation`](@ref) macro.

This function is a thin wrapper around the [`oapply`](@ref) method for
multispans, which implements the UWD algebra of multispans.
"""
function query(X::AbstractACSet, diagram::UndirectedWiringDiagram;
               table_type::Type=TypedTables.Table)
  spans = map(boxes(diagram), subpart(diagram, :name)) do b, name
    apex = FinSet(nparts(X, name))
    legs = map(subpart(diagram, ports(diagram, b), :port_name)) do port_name
      FinDomFunction(X, port_name == :_id ? name : port_name)
    end
    Multispan(apex, legs)
  end
  outer_names = subpart(diagram, :outer_port_name)
  outer_span = oapply(diagram, spans, Ob=SetOb, Hom=FinDomFunction{Int})
  table = NamedTuple{Tuple(outer_names)}(Tuple(map(collect, outer_span)))
  make_table(table_type, table)
end

end

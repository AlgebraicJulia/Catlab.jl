""" Algebras of operads of wiring diagrams.
"""
module WiringDiagramAlgebras
export oapply, query

using Requires

using ...Present, ...Theories
using ...Theories: dom_nums, codom_nums, attr, adom, adom_nums
using ...CategoricalAlgebra
import ...CategoricalAlgebra.CSets: homomorphisms, homomorphism, is_homomorphic
using ..UndirectedWiringDiagrams
using ..UndirectedWiringDiagrams: TheoryUWD

""" Compose morphisms according to UWD.

The morphisms corresponding to the boxes, and optionally also the objects
corresponding to the junctions, are given by dictionaries indexed by
box/junction attributes. The default attributes are those compatible with the
`@relation` macro.
"""
function oapply(composite::UndirectedWiringDiagram, hom_map::AbstractDict,
                ob_map::Union{AbstractDict,Nothing}=nothing;
                hom_attr::Symbol=:name, ob_attr::Symbol=:variable)
  # XXX: Julia should be inferring these vector eltypes but isn't on v1.7.
  homs = valtype(hom_map)[ hom_map[name] for name in composite[hom_attr] ]
  obs = isnothing(ob_map) ? nothing :
    valtype(ob_map)[ ob_map[name] for name in composite[ob_attr] ]
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
  for (j, foot) in enumerate(junction_feet)
    diagram[j, :ob₁] = L(foot)
  end

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

abstract type DataFrameFallback end
abstract type MaybeDataFrame <: DataFrameFallback end

""" Evaluate a conjunctive query on an attributed C-set.

The conjunctive query is represented as an undirected wiring diagram (UWD) whose
boxes and ports are named via the attributes `:name`, `:port_name`, and
`:outer_port_name`. To define such a diagram, use the [`@relation`](@ref) macro
with its named syntax. Parameters to the query may be passed as a collection of
pairs using the optional third argument.

The result is data table whose columns correspond to the outer ports of the UWD.
By default, a data frame is returned if the package
[`DataFrames.jl`](https://github.com/JuliaData/DataFrames.jl) is loaded;
otherwise, a named tuple is returned. To change this behavior, set the keyword
argument `table_type` to a type or function taking two arguments, a vector of
columns and a vector of column names. There is one exceptional case: if the UWD
has no outer ports, the query is a counting query and the result is a vector
whose length is the number of results.

For its implementation, this function wraps the [`oapply`](@ref) method for
multispans, which defines the UWD algebra of multispans.
"""
function query(X::ACSet, diagram::UndirectedWiringDiagram,
               params=(;); table_type=MaybeDataFrame)
  # For each box in the diagram, extract span from ACSet.
  spans = map(boxes(diagram), subpart(diagram, :name)) do b, name
    apex = FinSet(nparts(X, name))
    legs = map(subpart(diagram, ports(diagram, b), :port_name)) do port_name
      FinDomFunction(X, port_name == :_id ? name : port_name)
    end
    Multispan(apex, legs)
  end

  # Add an extra box and corresponding span for each parameter.
  if !isempty(params)
    diagram = copy(diagram)
    spans = vcat(spans, map_pairs(params) do (key, value)
      box = add_part!(diagram, :Box, name=:_const)
      junction = key isa Integer ? key : incident(diagram, key, :variable)
      add_part!(diagram, :Port, port_name=:_value,
                box=box, junction=junction)
      SMultispan{1}(ConstantFunction(value, FinSet(1)))
    end)
  end

  # Call `oapply` and make a table out of the resulting span.
  outer_span = oapply(diagram, spans, Ob=SetOb, Hom=FinDomFunction{Int})
  if nparts(diagram, :OuterPort) == 0
    fill((;), length(apex(outer_span)))
  else
    columns = map(collect, outer_span)
    names = has_subpart(diagram, :outer_port_name) ?
      subpart(diagram, :outer_port_name) : fill(nothing, length(columns))
    make_table(table_type, columns, names)
  end
end

map_pairs(f, collection) = map(f, collect(pairs(collection)))
map_pairs(f, vec::AbstractVector{<:Pair}) = map(f, vec)

""" Create conjunctive query (a UWD) for finding homomorphisms out of a C-set.

Returns the query together with query parameters for the attributes.
Homomorphisms from `X` to `Y` can be computed by:

```julia
query(Y, homomorphism_query(X)...)
```
"""
function homomorphism_query(X::StructACSet{S}; count::Bool=false) where S
  offsets = cumsum([0; [nparts(X,c) for c in ob(S)]])
  nelems = offsets[end]

  diagram = HomomorphismQueryDiagram{Symbol}()
  params = Pair[]
  add_parts!(diagram, :Junction, nelems)
  if !count
    add_parts!(diagram, :OuterPort, nelems, outer_junction=1:nelems)
  end
  for (i, c) in enumerate(ob(S))
    n = nparts(X,c)
    boxes = add_parts!(diagram, :Box, n, name=c)
    add_parts!(diagram, :Port, n, box=boxes, port_name=:_id,
               junction=(1:n) .+ offsets[i])
  end
  for (f, c, i, j) in zip(hom(S), dom(S), dom_nums(S), codom_nums(S))
    n = nparts(X,c)
    add_parts!(diagram, :Port, n, box=(1:n) .+ offsets[i], port_name=f,
               junction=X[:,f] .+ offsets[j])
  end
  for (f, c, i) in zip(attr(S), adom(S), adom_nums(S))
    n = nparts(X,c)
    junctions = add_parts!(diagram, :Junction, n)
    add_parts!(diagram, :Port, n, box=(1:n) .+ offsets[i], port_name=f,
               junction=junctions)
    append!(params, Iterators.map(Pair, junctions, X[:,f]))
  end
  (diagram, params)
end

@present TheoryHomomorphismQueryDiagram <: TheoryUWD begin
  Name::AttrType
  name::Attr(Box, Name)
  port_name::Attr(Port, Name)
end
@acset_type HomomorphismQueryDiagram(TheoryHomomorphismQueryDiagram,
  index=[:box, :junction, :outer_junction]) <: UndirectedWiringDiagram

function homomorphisms(X::ACSet, Y::ACSet, ::HomomorphismQuery)
  columns = query(Y, homomorphism_query(X)...; table_type=AbstractVector)
  map(row -> make_homomorphism(row, X, Y), eachrow(reduce(hcat, columns)))
end
function homomorphism(X::ACSet, Y::ACSet, ::HomomorphismQuery)
  columns = query(Y, homomorphism_query(X)...; table_type=AbstractVector)
  isempty(first(columns)) ? nothing :
    make_homomorphism(map(first, columns), X, Y)
end
function is_homomorphic(X::ACSet, Y::ACSet, ::HomomorphismQuery)
  length(query(Y, homomorphism_query(X, count=true)...)) > 0
end

function make_homomorphism(row, X::StructACSet{S}, Y::StructACSet{S}) where S
  components = let i = 0
    NamedTuple{ob(S)}([row[i+=1] for _ in parts(X,c)] for c in ob(S))
  end
  ACSetTransformation(components, X, Y)
end

make_table(f, columns, names) = f(columns, names)
make_table(::Type{AbstractVector}, columns, names) = columns
make_table(::Type{NamedTuple}, columns, names) =
  NamedTuple{Tuple(names)}(Tuple(columns))
make_table(::Type{<:DataFrameFallback}, columns, names) =
  make_table(NamedTuple, columns, names)

function __init__()
  @require DataFrames="a93c6f00-e57d-5684-b7b6-d8193f3e46c0" begin
    using .DataFrames: DataFrame
    make_table(::Type{MaybeDataFrame}, columns, names) =
      make_table(DataFrame, columns, names)
  end
end

end

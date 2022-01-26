module ACSetInterface
export ACSet, acset_schema,
  nparts, parts, has_part, has_subpart, subpart, incident,
  add_part!, add_parts!, set_subpart!, set_subparts!, rem_part!, rem_parts!,
  copy_parts!, copy_parts_only!, disjoint_union, tables, pretty_tables, @acset

using StaticArrays: StaticArray

using ..Syntax: GATExpr, args
using ..Theories: dom, codom
using ...Meta: strip_lines

using PrettyTables: pretty_table
using Tables

abstract type ACSet end

"""
Get the schema of an acset at runtime.
"""
function acset_schema end

""" Number of parts of given type in an acset.
"""
function nparts end

""" Parts of given type in an acset.
"""
@inline parts(acs, type) = 1:nparts(acs, type)

""" Whether an acset has a part with the given name.
"""
function has_part end

@inline has_part(acs, type::Symbol, part::Int) = 1 <= part <= nparts(acs, type)
@inline has_part(acs, type::Symbol, part::AbstractVector{Int}) =
  let n=nparts(acs, type); [ 1 <= x <= n for x in part ] end

function has_subpart end

""" Get subpart of part in acset.

Both single and vectorized access are supported, with a view of the underlying
data being returned in the latter case. Chaining, or composition, of subparts is
also supported. For example, given a vertex-attributed graph `g`,

```
subpart(g, e, [:src, :vattr])
```

returns the vertex attribute of the source vertex of the edge `e`. As a
shorthand, subparts can also be accessed by indexing:

```
g[e, :src] == subpart(g, e, :src)
```

Be warned that indexing with lists of subparts works just like `subpart`:
`g[e,[:src,:vattr]]` is equivalent to `subpart(g, e, [:src,:vattr])`. This
convention differs from DataFrames but note that the alternative interpretation
of `[:src,:vattr]` as two independent columns does not even make sense, since
they have different domains (belong to different tables).
"""
function  subpart end
@inline Base.@propagate_inbounds subpart(acs, part, name) = view_or_slice(subpart(acs, name), part)

function view_or_slice end
@inline view_or_slice(x::AbstractVector, i::Union{Integer,StaticArray}) = x[i]
@inline view_or_slice(x::AbstractVector, ::Colon) = x
@inline Base.@propagate_inbounds view_or_slice(x::AbstractVector, i) = @view x[i]

@inline subpart(acs, expr::GATExpr{:generator}) = subpart(acs, first(expr))
@inline subpart(acs, expr::GATExpr{:id}) = parts(acs, first(dom(expr)))

function subpart(acs, part, names::AbstractVector{Symbol})
  foldl(names, init=part) do part, name
    subpart(acs, part, name)
  end
end
subpart(acs, part, expr::GATExpr{:compose}) =
  subpart(acs, part, subpart_names(expr))

subpart(acs, names::AbstractVector{Symbol}) =
  subpart(acs, subpart(acs, names[1]), names[2:end])
subpart(acs, expr::GATExpr{:compose}) = subpart(acs, subpart_names(expr))

subpart_names(expr::GATExpr{:generator}) = Symbol[first(expr)]
subpart_names(expr::GATExpr{:id}) = Symbol[]
subpart_names(expr::GATExpr{:compose}) =
  mapreduce(subpart_names, vcat, args(expr))

""" Get superparts incident to part in acset.

If the subpart is indexed, this takes constant time; otherwise, it takes linear
time. As with [`subpart`](@ref), both single and vectorized access, as well as
chained access, are supported. Note that sequences of morphisms are supplied in
the usual left-to-right order, so that

```
incident(g, x, [:src, :vattr])
```

returns the list of all edges whose source vertex has vertex attribute `x`.

Note that when the subpart is indexed, this function returns a view of the
underlying index, which should not be mutated. To ensure that a fresh copy is
returned, regardless of whether indexing is enabled, set the keyword argument
`copy=true`.
"""
function incident end

function incident(acs, part, names::AbstractVector{Symbol};
                  copy::Bool=false)
  # Don't need to pass `copy` because copy will be made regardless.
  foldr(names, init=part) do name, part
    reduce(vcat, incident(acs, part, name), init=Int[])
  end
end

incident(acs, part, expr::GATExpr; kw...) =
  incident(acs, part, subpart_names(expr); kw...)

@inline add_part!(acs, type; kw...) = add_part!(acs, type, (;kw...))

""" Add part of given type to acset, optionally setting its subparts.

Returns the ID of the added part.

See also: [`add_parts!`](@ref).
"""
@inline function add_part!(acs, type::Symbol, kw)
  part = only(add_parts!(acs,type,1))
  try
    set_subparts!(acs, part, kw)
  catch e
    rem_part!(acs, type, part)
    rethrow(e)
  end
  part
end

""" Add parts of given type to acset, optionally setting their subparts.

Returns the range of IDs for the added parts.

See also: [`add_part!`](@ref).
"""
function add_parts! end

@inline add_parts!(acs, type::Symbol, n::Int; kw...) = add_parts!(acs, type, n, (;kw...))

@inline function add_parts!(acs, type::Symbol, n::Int, kw)
  parts = add_parts!(acs, type, n)
  try
    set_subparts!(acs, parts, kw)
  catch e
    rem_parts!(acs, type, parts)
    rethrow(e)
  end
  parts
end


""" Mutate subpart of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subparts!`](@ref).
"""
function set_subpart! end
@inline set_subpart!(acs, name, vals) = set_subpart!(acs, :, name, vals)

@inline set_subpart!(acs, ::Colon, name, vals) =
  set_subpart!(acs, 1:length(subpart(acs,name)), name, vals)

# Inlined for the same reason as `subpart`.

@inline function set_subpart!(acs, part::AbstractVector{Int}, name, vals)
  broadcast(part, vals) do part, vals
    set_subpart!(acs, part, name, vals)
  end
end

""" Mutate subparts of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subpart!`](@ref).
"""
@inline @generated function set_subparts!(acs, part, kw::NamedTuple{keys}) where {keys}
  Expr(:block,[:(set_subpart!(acs, part, $(Expr(:quote, name)), kw.$name)) for name in keys]...)
end

@inline set_subparts!(acs, part; kw...) = set_subparts!(acs, part, (;kw...))

""" Remove part from a C-set.

The part is removed using the "pop and swap" strategy familiar from
[LightGraphs.jl](https://github.com/JuliaGraphs/LightGraphs.jl), where the
"removed" part is actually replaced by the last part, which is then deleted.
This strategy has important performance benefits since only the last part must
be assigned a new ID, as opposed to assigning new IDs to *every* part following
the removed part.

The removal operation is *not* recursive. When a part is deleted, any superparts
incident to it are retained, but their subparts become undefined (equal to the
integer zero). For example, in a graph, if you call `rem_part!` on a vertex, the
edges incident the `src` and/or `tgt` vertices of the edge become undefined but
the edge itself is not deleted.

Indexing has both positive and negative impacts on performance. On the one hand,
indexing reduces the cost of finding affected superparts from linear time to
constant time. On the other hand, the indices of subparts must be updated when
the part is removed. For example, in a graph, indexing `src` and `tgt` makes
removing vertices faster but removing edges (slightly) slower.

See also: [`rem_parts!`](@ref).
"""
function rem_part! end

""" Remove parts from a C-set.

The parts must be supplied in sorted order, without duplicates.

See also: [`rem_part!`](@ref).
"""
@inline function rem_parts!(acs, type, parts)
  issorted(parts) || error("Parts to be removed must be in sorted order")
  for part in Iterators.reverse(parts)
    rem_part!(acs, type, part)
  end
end

""" Copy parts from a C-set to a C′-set.

The selected parts must belong to both schemas. All subparts common to the
selected parts, including data attributes, are preserved. Thus, if the selected
parts form a sub-C-set, then the whole sub-C-set is preserved. On the other
hand, if the selected parts do *not* form a sub-C-set, then some copied parts
will have undefined subparts.

TODO: handle colons
"""
function copy_parts! end

copy_parts!(to, from, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))

copy_parts!(to, from; kw...) = copy_parts!(to, from, (;kw...))

""" Copy parts from a C-set to a C′-set, ignoring all non-data subparts.

The selected parts must belong to both schemas. Attributes common to both
schemas are also copied, but no other subparts are copied.

See also: [`copy_parts!`](@ref).
"""
function copy_parts_only! end

function disjoint_union(acs1, acs2)
  acs = copy(acs1)
  copy_parts!(acs, acs2)
  acs
end

"""
Get a named tuple of Tables.jl-compatible tables from an acset
"""
function tables end

""" Display an ACSet prettily

This works for any acset that implements tables
"""

# Fancy Displaying

function pretty_tables(io::IO, acs::ACSet; kw...)
  options = merge((nosubheader=true, show_row_number=true), (; kw...))
  for (ob, table) in pairs(tables(acs))
    # Note: PrettyTables will not print tables with zero rows.
    if !(isempty(Tables.columnnames(table)) || Tables.rowcount(table) == 0)
      pretty_table(io, table, row_number_column_title=string(ob); options...)
    end
  end
end

pretty_tables(acs::ACSet; kw...) = pretty_tables(stdout, acs; kw...)

function Base.show(io::IO, ::MIME"text/plain", acs::T) where T <: ACSet
  print(io, T)
  print(io, " with elements ")
  join(io, ["$ob = $(parts(acs,ob))" for ob in keys(tables(acs))], ", ")
  println(io)
  pretty_tables(io, acs)
end

function Base.show(io::IO, ::MIME"text/html", acs::T) where T <: ACSet
  println(io, "<div class=\"c-set\">")
  print(io, "<span class=\"c-set-summary\">")
  print(io, T)
  print(io, " with elements ")
  join(io, ["$ob = $(parts(acs,ob))" for ob in keys(tables(acs))], ", ")
  println(io, "</span>")
  pretty_tables(io, acs, backend=Val(:html), standalone=false)
  println(io, "</div>")
end

macro acset(head, body)
  @assert body.head == :block
  vals = Expr(:call, :(Dict{Symbol,Any}))
  for l in strip_lines(body).args
    @assert l.head == :(=)
    push!(vals.args, :($(Expr(:quote, l.args[1])) => $(l.args[2])))
  end
  :(init_acset($(esc(head)), $(esc(vals))))
end

function init_acset(T::Type{<:ACSet}, initvals::Dict{Symbol,Any})
  acs = T()
  s = acset_schema(acs)
  ob_specs = filter((kv) -> kv[1] ∈ s.obs, pairs(initvals))
  hom_specs = filter((kv) -> kv[1] ∈ s.homs, pairs(initvals))
  attr_specs = filter((kv) -> kv[1] ∈ s.attrs, pairs(initvals))
  for (k,v) in ob_specs
    add_parts!(acs, k, Int(v))
  end
  for (k,v) in Iterators.flatten((hom_specs, attr_specs))
    set_subpart!(acs, :, k, collect_nonvector(v))
  end
  acs
end
collect_nonvector(v::AbstractVector) = v
collect_nonvector(v) = collect(v)

end

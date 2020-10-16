""" Data structure for C-sets (copresheaves) and attributed C-sets.
"""
module CSetDataStructures
export AbstractACSet, ACSet, AbstractCSet, CSet, Schema, FreeSchema,
  AbstractACSetType, ACSetType, ACSetTableType, AbstractCSetType, CSetType,
  tables, nparts, has_part, subpart, has_subpart, incident,
  add_part!, add_parts!, set_subpart!, set_subparts!, rem_part!, rem_parts!,
  copy_parts!, copy_parts_only!, disjoint_union

using Compat: isnothing, only

using PrettyTables: pretty_table
using StructArrays

using ...Theories: Schema, FreeSchema, dom, codom,
  CatDesc, CatDescType, AttrDesc, AttrDescType, SchemaType,
  ob_num, hom_num, data_num, attr_num, dom_num, codom_num
using ...Present

# Data types
############

""" Abstract type for attributed C-sets, including C-sets as a special case.

The type parameters are:

- `CD`: indexing category C, encoded as a type
- `AD`: data types and data attributes, encoded as a type
- `Ts`: Julia types corresponding to data types in schema

Together, the first two type parameters encode a schema, see `Schema`.

See also: [`AttributedCSet`](@ref).
"""
abstract type AbstractAttributedCSet{CD <: CatDesc, AD <: AttrDesc{CD},
                                     Ts <: Tuple} end

""" Alias for the abstract type `AbstractAttributedCSet`.
"""
const AbstractACSet = AbstractAttributedCSet

""" Data type for attributed C-sets, including C-sets as a special case.

Instead of filling out the type parameters manually, we recommend using the
function [`CSetType`](@ref) or [`ACSetType`](@ref) to generate a data type from
a schema. Nevertheless, the first three type parameters are documented at
[`AbstractAttributedCSet`](@ref). The remaining type parameters are
implementation details and should be ignored.
"""
struct AttributedCSet{CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,
                      Idxed, UniqueIdxed, Tables <: NamedTuple,
                      Indices <: NamedTuple} <: AbstractACSet{CD,AD,Ts}
  tables::Tables
  indices::Indices
  function AttributedCSet{CD,AD,Ts,Idxed,UniqueIdxed}() where
      {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed, UniqueIdxed}
    tables = make_tables(CD,AD,Ts)
    indices = make_indices(CD,AD,Ts,Idxed,UniqueIdxed)
    new{CD,AD,Ts,Idxed,UniqueIdxed,typeof(tables),typeof(indices)}(
      tables, indices)
  end
  function AttributedCSet{CD}() where {CD <: CatDesc}
    AttributedCSet{CD,typeof(AttrDesc(CD())),Tuple{}}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed,UniqueIdxed,Tables,Indices}() where
      {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed, UniqueIdxed,
       Tables <: NamedTuple, Indices <: NamedTuple}
    AttributedCSet{CD,AD,Ts,Idxed,UniqueIdxed}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed,UniqueIdxed,Tables,Indices}(
      tables::Tables, indices::Indices) where
      {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed, UniqueIdxed,
       Tables <: NamedTuple, Indices <: NamedTuple}
    new{CD,AD,Ts,Idxed,UniqueIdxed,Tables,Indices}(tables,indices)
  end
end

""" Alias for the data type `AttributedCSet`.
"""
const ACSet = AttributedCSet

""" Generate an abstract type for attributed C-sets from a schema.

To generate a concrete type, use [`ACSetType`](@ref).
"""
function AbstractACSetType(pres::Presentation{Schema})
  type_vars = [ TypeVar(nameof(data)) for data in generators(pres, :Data) ]
  if isempty(type_vars)
    # When the schema has no data attributes, allow subtyping from any schema
    # extending it with attributes.
    AbstractACSet{CatDescType(pres)}
  else
    T = AbstractACSet{SchemaType(pres)..., Tuple{type_vars...}}
    foldr(UnionAll, type_vars, init=T)
  end
end

""" Generate a type for attributed C-sets from a schema.

In addition to the schema, you can specify which morphisms and data attributes
are (uniquely) indexed using the keyword argument `index` (or `unique_index`).
By default, no morphisms or data attributes are indexed.

See also: [`AbstractACSetType`](@ref).
"""
function ACSetType(pres::Presentation{Schema}; index=[], unique_index=[])
  type_vars = [ TypeVar(nameof(data)) for data in generators(pres, :Data) ]
  T = ACSet{SchemaType(pres)..., Tuple{type_vars...},
            Tuple(sort!(index ∪ unique_index)), Tuple(sort!(unique_index))}
  foldr(UnionAll, type_vars, init=T)
end

""" Given an attributed C-set type, generate a new type based on one object.

The resulting attributed C-set type can be seen as the type of a data table or
data frame, hence the name.
"""
function ACSetTableType(X::Type, ob₀::Symbol; union_all::Bool=false)
  (union_all ? ACSetTableUnionAll : ACSetTableDataType)(X, Val(ob₀))
end

@generated function ACSetTableDataType(::Type{X}, ::Val{ob₀}) where
    {CD<:CatDesc, AD<:AttrDesc{CD}, Ts, X<:AbstractACSet{CD,AD,Ts}, ob₀}
  CD₀, AD₀ = ACSetTableDesc(CD, AD, ob₀)
  :(ACSet{$CD₀,$AD₀,$Ts,(),()})
end

@generated function ACSetTableUnionAll(::Type{X}, ::Val{ob₀}) where
    {CD<:CatDesc, AD<:AttrDesc{CD}, X<:AbstractACSet{CD,AD}, ob₀}
  CD₀, AD₀ = ACSetTableDesc(CD, AD, ob₀)
  :(ACSet{$CD₀,$AD₀,Tuple{$(AD.data...)},(),()} where {$(AD.data...)})
end

function ACSetTableDesc(::Type{CD}, ::Type{AD}, ob₀::Symbol) where
    {CD<:CatDesc, AD<:AttrDesc{CD}}
  @assert ob₀ ∈ CD.ob
  attrs₀ = [ i for (i,j) in enumerate(AD.adom) if CD.ob[j] == ob₀ ]
  adom = Tuple(ones(Int, length(attrs₀)))
  CD₀ = CatDesc{(ob₀,),(),(),()}
  AD₀ = AttrDesc{CD₀,AD.data,AD.attr[attrs₀],adom,AD.acodom[attrs₀]}
  (CD₀, AD₀)
end

""" Abstract type for C-sets.

The special case of `AbstractAttributedCSet` with no data attributes.
"""
const AbstractCSet{CD} = AbstractACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{}}

""" Data type for C-sets.

The special case of `AttributedCSet` with no data attributes.
"""
const CSet{CD,Idxed,UniqueIdxed} =
  ACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{},Idxed,UniqueIdxed}

""" Generate an abstract type for C-sets from a presentation of a category C.

To generate a concrete type, use [`CSetType`](@ref).
"""
function AbstractCSetType(pres::Presentation{Schema})
  AbstractCSet{CatDescType(pres)}
end

""" Generate a type for C-sets from a presentation of a category C.

In addition to the category, you can specify which morphisms are (uniquely)
indexed using the keyword argument `index` (or `unique_index`). By default, no
morphisms are indexed.

See also: [`AbstractCSetType`](@ref).
"""
function CSetType(pres::Presentation{Schema}; index=[], unique_index=[])
  CSet{CatDescType(pres),
       Tuple(sort!(index ∪ unique_index)), Tuple(sort!(unique_index))}
end

function make_indices(::Type{CD}, AD::Type{<:AttrDesc{CD}},
                      Ts::Type{<:Tuple}, Idxed::Tuple, UniqueIdxed::Tuple) where {CD}
  NamedTuple{Idxed}(Tuple(map(Idxed) do name
    IndexType = name ∈ UniqueIdxed ? Int : Vector{Int}
    if name ∈ CD.hom
      Vector{IndexType}()
    elseif name ∈ AD.attr
      Dict{Ts.parameters[codom_num(AD,name)],IndexType}()
    else
      error("Cannot index $name: not a morphism or an attribute")
    end
  end))
end

function make_tables(::Type{CD}, AD::Type{<:AttrDesc{CD}},
                     Ts::Type{<:Tuple}) where {CD}
  cols = NamedTuple{CD.ob}(Tuple{Symbol,Type}[] for ob in CD.ob)
  for hom in CD.hom
    push!(cols[dom(CD,hom)], (hom, Int))
  end
  for attr in AD.attr
    push!(cols[dom(AD,attr)], (attr, Ts.parameters[codom_num(AD,attr)]))
  end
  map(cols) do col
    SA = StructArray{NamedTuple{Tuple(first.(col)),Tuple{last.(col)...}}}
    make_struct_array(SA, undef, 0)
  end
end

const EmptyTuple = Union{Tuple{},NamedTuple{(),Tuple{}}}

""" Create StructArray while avoiding inconsistency with zero length arrays.

By default, just constructs a StructArray (a struct of arrays) but when the
struct is empty, returns a ordinary Julia vector (an array of empty structs).

For context, see: https://github.com/JuliaArrays/StructArrays.jl/issues/148
"""
make_struct_array(::Type{SA}, ::UndefInitializer, n::Int) where
  SA <: StructArray = SA(undef, n)
make_struct_array(::Type{<:StructArray{T}}, ::UndefInitializer, n::Int) where
  T <: EmptyTuple = fill(T(()), n)

function Base.:(==)(x1::T, x2::T) where T <: ACSet
  # The indices are redundant, so need not be compared.
  x1.tables == x2.tables
end

function Base.copy(acs::T) where T <: ACSet
  T(map(copy, acs.tables), map(copy, acs.indices))
end

function Base.show(io::IO, acs::T) where {CD,AD,Ts,T<:AbstractACSet{CD,AD,Ts}}
  print(io, T <: AbstractCSet ? "CSet" : "ACSet")
  println(io, "(")
  join(io, vcat(
    [ "  $ob = 1:$(nparts(acs,ob))" for ob in CD.ob ],
    [ "  $data = $(Ts.parameters[i])" for (i,data) in enumerate(AD.data) ],
    [ "  $hom : $(dom(CD,i)) → $(codom(CD,i)) = $(subpart(acs,hom))"
      for (i,hom) in enumerate(CD.hom) ],
    [ "  $attr : $(dom(AD,i)) → $(codom(AD,i)) = $(subpart(acs,attr))"
      for (i,attr) in enumerate(AD.attr) ],
  ), ",\n")
  print(io, ")")
end

function Base.show(io::IO, ::MIME"text/plain", acs::T) where {T<:AbstractACSet}
  print(io, T <: AbstractCSet ? "CSet" : "ACSet")
  print(io, " with elements ")
  join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in keys(tables(acs))], ", ")
  println(io)
  for (ob, table) in pairs(tables(acs))
    # Note: PrettyTables will not print tables with no rows or undefined elems.
    if !(eltype(table) <: EmptyTuple || isempty(table))
      # TODO: Set option `row_number_column_title=name` when next version of
      # PrettyTables is released, instead of making new table.
      cols = map(col -> replace_unassigned(col, "#undef"), fieldarrays(table))
      table = StructArray((; ob => 1:nparts(acs,ob), cols...))
      pretty_table(io, table, nosubheader=true)
    end
  end
end

function Base.show(io::IO, ::MIME"text/html", acs::T) where {T<:AbstractACSet}
  println(io, "<div class=\"c-set\">")
  print(io, "<span class=\"c-set-summary\">")
  print(io, T <: AbstractCSet ? "CSet" : "ACSet")
  print(io, " with elements ")
  join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in keys(tables(acs))], ", ")
  println(io, "</span>")
  for (ob, table) in pairs(tables(acs))
    # Note: PrettyTables will not print tables with no rows or undefined elems.
    if !(eltype(table) <: EmptyTuple || isempty(table))
      # TODO: Set option `row_number_column_title`. See above.
      cols = map(col -> replace_unassigned(col, "#undef"), fieldarrays(table))
      table = StructArray((; ob => 1:nparts(acs,ob), cols...))
      pretty_table(io, table, backend=:html, standalone=false, nosubheader=true)
    end
  end
  println(io, "</div>")
end

function replace_unassigned(x::Array{T}, value::V=nothing) where {T,V}
  y = Array{Union{T,V}}(undef, size(x))
  for i in eachindex(x)
    y[i] = isassigned(x, i) ? x[i] : value
  end
  y
end

# Imperative interface
######################

""" Tables defining a C-set.

A named tuple with a table for each part type. To ensure consistency, do not
directly mutate these tables, especially when indexing is enabled!
"""
tables(acs::ACSet) = acs.tables

""" Number of parts of given type in a C-set.
"""
nparts(acs::ACSet, type) = length(acs.tables[type])

""" Whether a C-set has a part with the given name.
"""
has_part(acs::ACSet, type::Symbol) = _has_part(acs, Val(type))

@generated function _has_part(::ACSet{CD,AD}, ::Val{type}) where {CD,AD,type}
  type ∈ CD.ob || type ∈ AD.data
end

has_part(acs::ACSet, type::Symbol, part::Int) = 1 <= part <= nparts(acs, type)
has_part(acs::ACSet, type::Symbol, part::AbstractVector{Int}) =
  let n=nparts(acs, type); [ 1 <= x <= n for x in part ] end

""" Whether a C-set has a subpart with the given name.
"""
has_subpart(acs::ACSet, name::Symbol) = _has_subpart(acs, Val(name))

@generated function _has_subpart(::ACSet{CD,AD}, ::Val{name}) where {CD,AD,name}
  name ∈ CD.hom || name ∈ AD.attr
end

""" Get subpart of part in C-set.

Both single and vectorized access are supported.
"""
subpart(acs::ACSet, part, name::Symbol) = subpart(acs,name)[part]
subpart(acs::ACSet, name::Symbol) = _subpart(acs,Val(name))

@generated function _subpart(acs::ACSet{CD,AD,Ts}, ::Val{name}) where
    {CD,AD,Ts,name}
  if name ∈ CD.hom
    :(acs.tables.$(dom(CD,name)).$name)
  elseif name ∈ AD.attr
    :(acs.tables.$(dom(AD,name)).$name)
  else
    throw(KeyError(name))
  end
end

""" Get superparts incident to part in C-set.

If the subpart is indexed, this takes constant time; otherwise, it takes linear
time. Both single and vectorized access are supported.
"""
incident(acs::ACSet, part, name::Symbol) = _incident(acs, part, Val(name))

@generated function _incident(acs::ACSet{CD,AD,Ts,Idxed}, part, ::Val{name}) where
    {CD,AD,Ts,Idxed,name}
  if name ∈ CD.hom
    if name ∈ Idxed
      :(acs.indices.$name[part])
    else
      :(broadcast_findall(part, acs.tables.$(dom(CD,name)).$name))
    end
  elseif name ∈ AD.attr
    if name ∈ Idxed
      :(get_data_index.(Ref(acs.indices.$name), part))
    else
      :(broadcast_findall(part, acs.tables.$(dom(AD,name)).$name))
    end
  else
    throw(KeyError(name))
  end
end

broadcast_findall(xs, array::AbstractArray) =
  broadcast(x -> findall(y -> x == y, array), xs)

""" Add part of given type to C-set, optionally setting its subparts.

Returns the ID of the added part.

See also: [`add_parts!`](@ref).
"""
function add_part!(acs::ACSet, type::Symbol, args...; kw...)
  part = only(_add_parts!(acs, Val(type), 1))
  set_subparts!(acs, part, args...; kw...)
  part
end

""" Add parts of given type to C-set, optionally setting their subparts.

Returns the range of IDs for the added parts.

See also: [`add_part!`](@ref).
"""
function add_parts!(acs::ACSet, type::Symbol, n::Int, args...; kw...)
  parts = _add_parts!(acs, Val(type), n)
  set_subparts!(acs, parts, args...; kw...)
  parts
end

@generated function _add_parts!(acs::ACSet{CD,AD,Ts,Idxed}, ::Val{ob},
                                n::Int) where {CD,AD,Ts,Idxed,ob}
  out_homs = filter(hom -> dom(CD, hom) == ob, CD.hom)
  indexed_in_homs = filter(hom -> codom(CD, hom) == ob && hom ∈ Idxed, CD.hom)
  quote
    if n == 0; return 1:0 end
    nparts = length(acs.tables.$ob) + n
    resize!(acs.tables.$ob, nparts)
    start = nparts - n + 1
    $(Expr(:block, map(out_homs) do hom
        :(@inbounds acs.tables.$ob.$hom[start:nparts] .= 0)
     end...))
    $(Expr(:block, map(indexed_in_homs) do hom
        quote
          resize!(acs.indices.$hom, nparts)
          @inbounds for i in start:nparts; acs.indices.$hom[i] = Int[] end
        end
      end...))
    start:nparts
  end
end

""" Mutate subpart of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subparts!`](@ref).
"""
set_subpart!(acs::ACSet, part::Int, name, subpart) =
  _set_subpart!(acs, part, Val(name), subpart)

function set_subpart!(acs::ACSet, part::AbstractVector{Int},
                      name::Symbol, subpart)
  broadcast(part, subpart) do part, subpart
    _set_subpart!(acs, part, Val(name), subpart)
  end
end

set_subpart!(acs::ACSet, ::Colon, name::Symbol, subpart) =
  set_subpart!(acs, name, subpart)
set_subpart!(acs::ACSet, name::Symbol, new_subpart) =
  set_subpart!(acs, 1:length(subpart(acs, name)), name, new_subpart)

@generated function _set_subpart!(acs::ACSet{CD,AD,Ts,Idxed}, part::Int,
    ::Val{name}, subpart) where {CD,AD,Ts,Idxed,name}
  if name ∈ CD.hom
    ob, codom_ob = dom(CD, name), codom(CD, name)
    if name ∈ Idxed
      quote
        @assert 0 <= subpart <= length(acs.tables.$codom_ob)
        old = acs.tables.$ob.$name[part]
        acs.tables.$ob.$name[part] = subpart
        if old > 0
          @assert deletesorted!(acs.indices.$name[old], part)
        end
        if subpart > 0
          insertsorted!(acs.indices.$name[subpart], part)
        end
      end
    else
      quote
        @assert 0 <= subpart <= length(acs.tables.$codom_ob)
        acs.tables.$ob.$name[part] = subpart
      end
    end
  elseif name ∈ AD.attr
    ob = dom(AD, name)
    if name ∈ Idxed
      quote
        if isassigned(acs.tables.$ob.$name, part)
          old = acs.tables.$ob.$name[part]
          unset_data_index!(acs.indices.$name, old, part)
        end
        acs.tables.$ob.$name[part] = subpart
        set_data_index!(acs.indices.$name, subpart, part)
      end
    else
      :(acs.tables.$ob.$name[part] = subpart)
    end
  else
    throw(KeyError(name))
  end
end

""" Mutate subparts of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subpart!`](@ref).
"""
set_subparts!(acs::ACSet, part; kw...) = set_subparts!(acs, part, (; kw...))

function set_subparts!(acs::ACSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(acs, part, name, subpart)
  end
end

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
the parted is remove. For example, in a graph, indexing `src` and `tgt` makes
removing vertices faster but removing edges (slightly) slower.

See also: [`rem_parts!`](@ref).
"""
rem_part!(acs::ACSet, type::Symbol, part::Int) =
  _rem_part!(acs, Val(type), part)

@generated function _rem_part!(acs::ACSet{CD,AD,Ts,Idxed}, ::Val{ob},
                               part::Int) where {CD,AD,Ts,Idxed,ob}
  in_homs = filter(hom -> codom(CD, hom) == ob, CD.hom)
  indexed_out_homs = filter(hom -> dom(CD, hom) == ob && hom ∈ Idxed, CD.hom)
  indexed_attrs = filter(attr -> dom(AD, attr) == ob && attr ∈ Idxed, AD.attr)
  quote
    last_part = length(acs.tables.$ob)
    @assert 1 <= part <= last_part
    # Unassign superparts of the part to be removed and also reassign superparts
    # of the last part to this part.
    for hom in $(Tuple(in_homs))
      set_subpart!(acs, incident(acs, part, hom), hom, 0)
      set_subpart!(acs, copy(incident(acs, last_part, hom)), hom, part)
    end
    last_row = acs.tables.$ob[last_part]

    # Clear any morphism and data attribute indices for last part.
    for hom in $(Tuple(indexed_out_homs))
      set_subpart!(acs, last_part, hom, 0)
    end
    for attr in $(Tuple(indexed_attrs))
      unset_data_index!(acs.indices[attr], last_row[attr], last_part)
    end

    # Finally, delete the last part and update subparts of the removed part.
    resize!(acs.tables.$ob, last_part - 1)
    if part < last_part
      set_subparts!(acs, part, last_row)
    end
  end
end

""" Remove parts from a C-set.

The parts must be supplied in sorted order, without duplicates.

See also: [`rem_part!`](@ref).
"""
function rem_parts!(acs::ACSet, type::Symbol, parts::AbstractVector{Int})
  issorted(parts) || error("Parts to removed must be in sorted order")
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
"""
@generated function copy_parts!(to::ACSet{CD},
                                from::ACSet{CD′}; kw...) where {CD, CD′}
  obs = intersect(CD.ob, CD′.ob)
  :(copy_parts!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

copy_parts!(to::ACSet, from::ACSet, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))
copy_parts!(to::ACSet, from::ACSet, parts::NamedTuple) =
  _copy_parts!(to, from, replace_colons(from, parts))

@generated function _copy_parts!(to::ACSet{CD}, from::ACSet{CD′},
                                 parts::NamedTuple{obs}) where {CD, CD′, obs}
  @assert obs ⊆ intersect(CD.ob, CD′.ob)
  homs = intersect(CD.hom, CD′.hom)
  homs = filter(homs) do hom
    c, c′, d, d′ = dom(CD,hom), dom(CD′,hom), codom(CD,hom), codom(CD′,hom)
    c == c′ && d == d′ && c ∈ obs && d ∈ obs
  end
  hom_triples = [ (hom, dom(CD,hom), codom(CD,hom)) for hom in homs ]
  in_obs = unique!(map(last, hom_triples))
  quote
    newparts = _copy_parts_only!(to, from, parts)
    partmaps = NamedTuple{$(Tuple(in_obs))}(tuple($(map(in_obs) do type
      :(Dict{Int,Int}(zip(parts.$type, newparts.$type)))
    end...)))
    for (name, dom, codom) in $(Tuple(hom_triples))
      for (p, newp) in zip(parts[dom], newparts[dom])
        q = subpart(from, p, name)
        newq = get(partmaps[codom], q, nothing)
        if !isnothing(newq)
          set_subpart!(to, newp, name, newq)
        end
      end
    end
    newparts
  end
end

""" Copy parts from a C-set to a C′-set, ignoring all non-data subparts.

The selected parts must belong to both schemas. Data attributes common to both
schemas are also copied, but no other subparts are copied.

See also: [`copy_parts!`](@ref).
"""
@generated function copy_parts_only!(to::ACSet{CD},
                                     from::ACSet{CD′}; kw...) where {CD, CD′}
  obs = intersect(CD.ob, CD′.ob)
  :(copy_parts_only!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

copy_parts_only!(to::ACSet, from::ACSet, obs::Tuple) =
  copy_parts_only!(to, from, NamedTuple{obs}((:) for ob in obs))
copy_parts_only!(to::ACSet, from::ACSet, parts::NamedTuple) =
  _copy_parts_only!(to, from, replace_colons(from, parts))

@generated function _copy_parts_only!(to::ACSet{CD,AD}, from::ACSet{CD′,AD′},
    parts::NamedTuple{obs}) where {CD, AD, CD′, AD′, obs}
  @assert obs ⊆ intersect(CD.ob, CD′.ob)
  attrs = intersect(AD.attr, AD′.attr)
  attrs = filter(attrs) do attr
    ob, ob′ = dom(AD, attr), dom(AD′, attr)
    ob == ob′ && ob ∈ obs
  end
  Expr(:block,
    :(newparts = (; $(map(obs) do ob
        Expr(:kw, ob, :(add_parts!(to, $(QuoteNode(ob)), length(parts.$ob))))
        end...))),
    map(attrs) do attr
      ob = dom(AD, attr)
      :(set_subpart!(to, newparts.$ob, $(QuoteNode(attr)),
                     subpart(from, parts.$ob, $(QuoteNode(attr)))))
    end...,
    :newparts)
end

function replace_colons(acs::ACSet, parts::NamedTuple{types}) where {types}
  NamedTuple{types}(map(types, parts) do type, part
    part == (:) ? (1:nparts(acs, type)) : part
  end)
end

function disjoint_union(acs1::T, acs2::T) where {T<:ACSet}
  acs = copy(acs1)
  copy_parts!(acs, acs2)
  acs
end

""" Look up key in C-set data index.
"""
get_data_index(d::AbstractDict{K,Int}, k::K) where K = get(d, k, 0)
get_data_index(d::AbstractDict{K,<:AbstractVector{Int}}, k::K) where K =
  get(d, k, 1:0)

""" Set key and value for C-set data index.
"""
function set_data_index!(d::AbstractDict{K,Int}, k::K, v::Int) where K
  if haskey(d, k)
    error("Key $k already defined in unique index")
  end
  d[k] = v
end
function set_data_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                         k::K, v::Int) where K
  insertsorted!(get!(d, k) do; Int[] end, v)
end

""" Unset key and value from C-set data index, if it is set.
"""
function unset_data_index!(d::AbstractDict{K,Int}, k::K, v::Int) where K
  if haskey(d, k) && d[k] == v
    delete!(d, k)
  end
end
function unset_data_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                           k::K, v::Int) where K
  if haskey(d, k)
    vs = d[k]
    if deletesorted!(vs, v) && isempty(vs)
      delete!(d, k)
    end
  end
end

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector, if present.

Returns whether an occurence was found and deleted.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  found = i <= length(a) && a[i] == x
  if found; deleteat!(a, i) end
  found
end

end

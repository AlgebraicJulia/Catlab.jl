module CSetDataStructures
export @acset_type, @abstract_acset_type, @declare_schema, FreeSchema,
  StructACSet, StructCSet, ACSetTableType

using MLStyle
using StaticArrays
using Reexport
import Tables

@reexport using ..ACSetInterface
using ..IndexUtils
using ...Theories, ...Present, ...Syntax
using ...Theories: FreeSchema, SchemaDesc, SchemaDescType, CSetSchemaDescType,
  SchemaDescTypeType, ob_num, codom_num, attr, attrtype
import ...Present: Presentation

# StructACSet Struct Generation
###############################

abstract type StructACSet{S<:SchemaDescType,Ts<:Tuple,Idxed,UniqueIdxed} <: ACSet end

const StructCSet = StructACSet{S,Tuple{},Idxed,UniqueIdxed} where
  {S<:CSetSchemaDescType,Idxed,UniqueIdxed}

q(s::Symbol) = Expr(:quote,s)
q(s::GATExpr) = q(nameof(s))

""" Creates a quoted named tuple used for `StructACSet`s
"""
function pi_type(dom::Vector, F::Function)
  :(NamedTuple{($(q.(dom)...),),Tuple{$(F.(dom)...)}})
end

""" Creates a quoted element of a named tuple used for `StructACSet`s
"""
function pi_type_elt(dom::Vector, f::Function)
  if length(dom) > 0
    Expr(:tuple, Expr(:parameters, [Expr(:kw, nameof(d), f(d)) for d in dom]...))
  else # workaround for Julia 1.0
    :(NamedTuple())
  end
end

""" Create the struct declaration for a `StructACSet` from a Presentation
"""
function struct_acset(name::Symbol, parent, p::Presentation{Schema};
                      index=[], unique_index=[])
  obs = p.generators[:Ob]
  homs = p.generators[:Hom]
  attr_types = p.generators[:AttrType]
  Ts = nameof.(attr_types)
  attrs = p.generators[:Attr]
  idxed = (;[x => x ∈ index for x in [nameof.(homs);nameof.(attrs)]]...)
  unique_idxed = (;[x => x ∈ unique_index for x in [nameof.(homs);nameof.(attrs)]]...)
  indexed_homs = filter(f -> idxed[nameof(f)], homs)
  unique_indexed_homs = filter(f -> unique_idxed[nameof(f)], homs)
  indexed_attrs = filter(a -> idxed[nameof(a)], attrs)
  unique_indexed_attrs = filter(a -> unique_idxed[nameof(a)], attrs)
  parameterized_type, new_call = if length(attr_types) > 0
    (:($name{$(nameof.(attr_types)...)}), :(new{$(nameof.(attr_types)...)}))
  else
    name, :new
  end
  schema_type = SchemaDescTypeType(p)
  obs_t = :($(GlobalRef(StaticArrays, :MVector)){$(length(obs)), Int})
  quote
    struct $parameterized_type <: $parent{$schema_type, Tuple{$(Ts...)}, $idxed, $unique_idxed}
      obs::$obs_t
      homs::$(pi_type(homs, _ -> :(Vector{Int})))
      attrs::$(pi_type(attrs, a -> :(Vector{$(nameof(codom(a)))})))
      hom_indices::$(pi_type(indexed_homs, _ -> :(Vector{Vector{Int}})))
      hom_unique_indices::$(pi_type(unique_indexed_homs, _ -> :(Vector{Int})))
      attr_indices::$(pi_type(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}})))
      attr_unique_indices::$(pi_type(unique_indexed_attrs, a -> :(Dict{$(nameof(codom(a))), Int})))
      function $parameterized_type() where {$(nameof.(attr_types)...)}
        $new_call(
          $obs_t(zeros(Int, $(length(obs)))),
          $(pi_type_elt(homs, _ -> :(Int[]))),
          $(pi_type_elt(attrs, a -> :($(nameof(codom(a)))[]))),
          $(pi_type_elt(indexed_homs, _ -> :(Vector{Int}[]))),
          $(pi_type_elt(unique_indexed_homs, _ -> :(Int[]))),
          $(pi_type_elt(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}}()))),
          $(pi_type_elt(unique_indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Int}())))
        )
      end
    end
  end
end

unquote(x::QuoteNode) = x.value

macro acset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructACSet))
  end
  name, schema, idx_args = @match head begin
    Expr(:call, name, schema, idx_args...) => (name, schema, idx_args)
    _ => error("Unsupported head for @acset_type")
  end
  quote
    $(esc(:eval))($(GlobalRef(CSetDataStructures, :struct_acset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema));
      $((esc(arg) for arg in idx_args)...)))
    Core.@__doc__ $(esc(name))
  end
end

macro abstract_acset_type(head)
  type, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructACSet))
  end
  esc(quote
    abstract type $type{S,Ts,Idxed,UniqueIdxed} <: $parent{S,Ts,Idxed,UniqueIdxed} end
  end)
end

# StructACSet DataFrames
########################

struct StructACSetFrame{Ob, S, Ts, Idxed, UniqueIdxed, Attrs} <:
    StructACSet{S, Ts, Idxed, UniqueIdxed}
  obs::MVector{1,Int}
  homs::NamedTuple{(),Tuple{}}
  attrs::Attrs
  hom_indices::NamedTuple{(),Tuple{}}
  hom_unique_indices::NamedTuple{(),Tuple{}}
  attr_indices::NamedTuple{(),Tuple{}}
  attr_unique_indices::NamedTuple{(),Tuple{}}
  function StructACSetFrame{Ob, S, Ts, Idxed, UniqueIdxed, Attrs}() where
      {Ob,S,Ts,Idxed,UniqueIdxed,Attrs}
    new{Ob,S,Ts,Idxed,UniqueIdxed,Attrs}(
      MVector(0),
      (;),
      Attrs([[] for a in attr(S)]),
      (;),
      (;),
      (;),
      (;)
    )
  end
end

function ACSetTableDesc(::Type{S}, ob::Symbol) where {S}
  s = SchemaDesc(S)
  attrs = filter(s.attrs) do attr
    s.doms[attr] == ob
  end
  doms = filter(s.doms) do (f,i)
    f ∈ attrs
  end
  codoms = filter(s.codoms) do (f,i)
    f ∈ attrs
  end
  s′ = SchemaDesc([ob], Symbol[], s.attrtypes, attrs, doms, codoms)
  SchemaDescTypeType(s′)
end

function ACSetTableDataType(::Type{<:StructACSet{S,Ts}}, ob::Symbol) where {S,Ts}
  S′ = ACSetTableDesc(S,ob)
  rowtype = NamedTuple{
    attr(S′),
    Tuple{[Vector{Ts.parameters[codom_num(S′,a)]} for a in attr(S′)]...}
  }
  StructACSetFrame{(ob,), S′, Ts,
                   NamedTuple(a => false for a in attr(S′)),
                   NamedTuple(a => false for a in attr(S′)),
                   rowtype}
end

function ACSetTableUnionAll(::Type{<:StructACSet{S}}, ob::Symbol) where {S}
  S′ = ACSetTableDesc(S,ob)
  type_vars = [ TypeVar(at) for at in attrtype(S′) ]
  rowtype = NamedTuple{
    attr(S′),
    Tuple{[Vector{type_vars[codom_num(S′,a)]} for a in attr(S′)]...}
  }
  T = StructACSetFrame{(ob,), S′, Tuple{type_vars...},
                       NamedTuple(a => false for a in attr(S′)),
                       NamedTuple(a => false for a in attr(S′)),
                       rowtype}
  foldr(UnionAll, type_vars, init=T)
end

function ACSetTableType(X::Type, ob::Symbol; union_all::Bool=false)
  (union_all ? ACSetTableUnionAll : ACSetTableDataType)(X, ob)
end

# StructACSet Operations
########################

Presentation(::Type{<:StructACSet{S}}) where S = Presentation(S)
Presentation(::StructACSet{S}) where S = Presentation(S)

# Accessors
###########

function Base.:(==)(x1::T, x2::T) where T <: StructACSet
  # The indices hold redundant information, so need not be compared.
  unref(x) = x[]
  unref.(values(x1.obs)) == unref.(values(x2.obs)) && x1.homs == x2.homs && x1.attrs == x2.attrs
end

ACSetInterface.acset_schema(::StructACSet{S}) where {S} = SchemaDesc(S)

@inline ACSetInterface.nparts(acs::StructACSet, ob::Symbol) = _nparts(acs, Val{ob})

@generated function _nparts(acs::StructACSet{S}, ::Type{Val{ob}}) where {S,ob}
  :(acs.obs[$(ob_num(S,ob))])
end

@inline ACSetInterface.has_part(acs::StructACSet, ob::Symbol) = _has_part(acs, Val{ob})

outgoing(acs::StructACSet, ob::Symbol) = _outgoing(acs, Val{ob})

@generated function _outgoing(::StructACSet{S}, ::Type{Val{ob}}) where {S,ob}
  s = SchemaDesc(S)
  Tuple(filter(f -> s.doms[f] == ob, vcat(s.homs,s.attrs)))
end

@generated function _has_part(acs::StructACSet{S}, ::Type{Val{ob}}) where
  {obs, S <: SchemaDescType{obs}, ob}
  ob ∈ obs
end

@inline ACSetInterface.has_subpart(acs::StructACSet, f::Symbol) = _has_subpart(acs, Val{f})

@generated function _has_subpart(acs::StructACSet{S}, ::Type{Val{f}}) where
  {f, obs, homs, attrtypes, attrs, S <: SchemaDescType{obs,homs,attrtypes,attrs}}
  f ∈ homs || f ∈ attrs
end

@inline ACSetInterface.subpart(acs::StructACSet, f::Symbol) = _subpart(acs,Val{f})

@generated function _subpart(acs::StructACSet{S}, ::Type{Val{f}}) where {S,f}
  s = SchemaDesc(S)
  if f ∈ s.homs
    :(acs.homs.$f)
  elseif f ∈ s.attrs
    :(acs.attrs.$f)
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs) or $(s.attrs)"))
  end
end

@inline Base.getindex(acs::StructACSet, args...) = ACSetInterface.subpart(acs, args...)

@inline ACSetInterface.incident(acs::StructACSet, part, f::Symbol; copy::Bool=false) =
  _incident(acs, part, Val{f}, Val{copy})

broadcast_findall(xs, array::AbstractArray) =
  broadcast(x -> findall(y -> x == y, array), xs)

function get_attr_index(idx::AbstractDict, k)
  get(idx, k, [])
end
function get_attr_index(idx::AbstractDict, k::AbstractArray)
  get_attr_index.(Ref(idx), k)
end

"""
We keep the main body of the code generating out of the @generated function
so that the code-generating function only needs to be compiled once.
"""
function incident_body(s::SchemaDesc, idxed::AbstractDict{Symbol,Bool},
                       unique_idxed::AbstractDict{Symbol,Bool}, f::Symbol,
                       copy::Bool)
  if f ∈ s.homs
    if idxed[f]
      quote
        indices = $(GlobalRef(ACSetInterface,:view_or_slice))(acs.hom_indices.$f, part)
        $(copy ? :(Base.copy.(indices)) : :(indices))
      end
    elseif unique_idxed[f]
      quote
        indices = $(GlobalRef(ACSetInterface,:view_or_slice))(acs.hom_unique_indices.$f, part)
        $(copy ? :(Base.copy.(indices)) : :(indices))
      end
    else
      :(broadcast_findall(part, acs.homs.$f))
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        indices = get_attr_index(acs.attr_indices.$f, part)
        $(copy ? :(Base.copy.(indices)) : :(indices))
      end
    elseif unique_idxed[f]
      quote
        get.(Ref(acs.attr_unique_indices.$f), part, Ref(0))
      end
    else
      :(broadcast_findall(part, acs.attrs.$f))
    end
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs)"))
  end
end

@generated function _incident(acs::StructACSet{S,Ts,Idxed,UniqueIdxed},
                              part, ::Type{Val{f}}, ::Type{Val{copy}}) where
  {S,Ts,Idxed,UniqueIdxed,f,copy}
  incident_body(SchemaDesc(S),pairs(Idxed),pairs(UniqueIdxed),f,copy)
end

# Mutators
##########

"""
This is a specialized function to add parts to an ACSet and preallocate the indices of
morphisms leading from those parts. This is useful if you want to reduce your
total number of allocations when allocating an acset if you already know ahead of
time a reasonable bound on the size of the preimages of the morphisms that you are using.

For instance, if you are making a cyclic graph, then you know that the preimages of
src and tgt will all be of size 1, and hence you can avoid allocating a zero-size
array, and then again allocating a 1-size array and instead just allocate a
1-size array off the bat.

This function is currently exposed, but is not well-integrated with wrappers
around add_parts; only use this if you really need it for performance and
understand what you are doing. Additionally, the only guarantee w.r.t. to this
is that it works the same semantically as `add_parts!`; it might make your code
faster, but it also might not. Only use this if you have the benchmarks to back
it up.
"""
@inline add_parts_with_indices!(acs::StructACSet, ob::Symbol, n::Int, index_sizes::NamedTuple) =
  _add_parts!(acs, Val{ob}, n, index_sizes)

@inline ACSetInterface.add_parts!(acs::StructACSet, ob::Symbol, n::Int) =
  _add_parts!(acs, Val{ob}, n, (;))

function add_parts_body(s::SchemaDesc, idxed::AbstractDict,
                        unique_idxed::AbstractDict, ob::Symbol,
                        index_sized_homs::Vector)
  code = quote
    m = acs.obs[$(ob_num(s, ob))]
    nparts = m + n
    newparts = (m+1):m+n
    acs.obs[$(ob_num(s, ob))] = nparts
  end
  for f in s.homs
    if s.doms[f] == ob
      push!(code.args, quote
              resize!(acs.homs.$f, nparts)
              acs.homs.$f[newparts] .= 0
            end)
    end
    if s.codoms[f] == ob && idxed[f]
      size = if f ∈ index_sized_homs
        :(index_sizes[$(Expr(:quote, f))])
      else
        0
      end
      push!(code.args, quote
            resize!(acs.hom_indices.$f, nparts)
            for i in newparts
              acs.hom_indices.$f[i] = Array{Int}(undef, $size)
              empty!(acs.hom_indices.$f[i])
            end
            end)
    elseif s.codoms[f] == ob && unique_idxed[f]
      push!(code.args, quote
            resize!(acs.hom_unique_indices.$f, nparts)
            for i in newparts
              acs.hom_unique_indices.$f[i] = 0
            end
            end)
    end
    code
  end
  for a in s.attrs
    if s.doms[a] == ob
      push!(code.args,:(resize!(acs.attrs.$a, nparts)))
    end
  end
  push!(code.args, :(return newparts))
  code
end

""" This generates the _add_parts! methods for a specific object of a `StructACSet`.
"""
@generated function _add_parts!(acs::StructACSet{S,Ts,Idxed,UniqueIdxed},
                                ::Type{Val{ob}}, n::Int,
                                index_sizes::NamedTuple{index_sized_homs}) where
  {S, Ts, Idxed, UniqueIdxed, ob, index_sized_homs}
  add_parts_body(SchemaDesc(S),pairs(Idxed),pairs(UniqueIdxed),ob,[index_sized_homs...])
end

@inline ACSetInterface.set_subpart!(acs::StructACSet, part::Int, f::Symbol, subpart) =
  _set_subpart!(acs, part, Val{f}, subpart)


function set_subpart_body(s::SchemaDesc, idxed::AbstractDict{Symbol,Bool},
                          unique_idxed::AbstractDict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        @assert 0 <= subpart <= acs.obs[$(ob_num(s, s.codoms[f]))]
        @inbounds old = acs.homs.$f[part]
        @inbounds acs.homs.$f[part] = subpart
        if old > 0
          @assert deletesorted!(acs.hom_indices.$f[old], part)
        end
        if subpart > 0
          insertsorted!(acs.hom_indices.$f[subpart], part)
        end
        subpart
      end
    elseif unique_idxed[f]
      quote
        @assert 0 <= subpart <= acs.obs[$(ob_num(s, s.codoms[f]))]
        @assert acs.hom_unique_indices.$f[subpart] == 0
        old = acs.homs.$f[part]
        if old > 0
          acs.hom_unique_indices.$f[old] = 0
        end
        acs.homs.$f[part] = subpart
        acs.hom_unique_indices.$f[subpart] = part
        subpart
      end
    else
      quote
        @assert 0 <= subpart <= acs.obs[$(ob_num(s, s.codoms[f]))]
        acs.homs.$f[part] = subpart
        subpart
      end
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        if isassigned(acs.attrs.$f, part)
          old = acs.attrs.$f[part]
          unset_attr_index!(acs.attr_indices.$f, old, part)
        end
        acs.attrs.$f[part] = subpart
        set_attr_index!(acs.attr_indices.$f, subpart, part)
        subpart
      end
    elseif unique_idxed[f]
      quote
        @boundscheck @assert subpart ∉ keys(acs.attr_unique_indices.$f) "subpart not unique"
        if isassigned(acs.attrs.$f, part)
          old = acs.attrs.$f[part]
          delete!(acs.attr_unique_indices.$f, old)
        end
        acs.attrs.$f[part] = subpart
        acs.attr_unique_indices.$f[subpart] = part
        subpart
      end
    else
      :(acs.attrs.$f[part] = subpart)
    end
  else
    throw(ArgumentError("$(f) not in $(s.homs) or $(s.attrs)"))
  end
end

""" This generates the `_set_subparts!` method for a specific arrow (hom/attr) of a StructACSet
"""
@generated function _set_subpart!(acs::StructACSet{S,Ts,Idxed,UniqueIdxed},
                                  part, ::Type{Val{f}}, subpart) where {S,Ts,Idxed,UniqueIdxed,f}
  set_subpart_body(SchemaDesc(S),pairs(Idxed),pairs(UniqueIdxed),f)
end

@inline Base.setindex!(acs::StructACSet, val, ob, part) = set_subpart!(acs, ob, part, val)

@inline Base.setindex!(acs::StructACSet, val, ob) = set_subpart!(acs, ob, val)

@inline ACSetInterface.rem_part!(acs::StructACSet, type::Symbol, part::Int) =
  _rem_part!(acs, Val{type}, part)

function rem_part_body(s::SchemaDesc, idxed, ob::Symbol)
  in_homs = filter(hom -> s.codoms[hom] == ob, s.homs)
  out_homs = filter(f -> s.doms[f] == ob, s.homs)
  out_attrs = filter(f -> s.doms[f] == ob, s.attrs)
  indexed_out_homs = filter(hom -> s.doms[hom] == ob && idxed[hom], s.homs)
  indexed_attrs = filter(attr -> s.doms[attr] == ob && idxed[attr], s.attrs)
  quote
    last_part = @inbounds acs.obs[$(ob_num(s, ob))]
    @assert 1 <= part <= last_part
    # Unassign superparts of the part to be removed and also reassign superparts
    # of the last part to this part.
    for hom in $(Tuple(in_homs))
      set_subpart!(acs, incident(acs, part, hom, copy=true), hom, 0)
      set_subpart!(acs, incident(acs, last_part, hom, copy=true), hom, part)
    end

    # This is a hack to avoid allocating a named tuple, because these parts
    # are a union type, so there would be dynamic dispatch
    $(Expr(:block, (map([out_homs; out_attrs]) do f
         :($(Symbol("last_row_" * string(f))) =
           if isassigned(subpart(acs, $(Expr(:quote,f))), last_part)
             subpart(acs, last_part, $(Expr(:quote,f)))
           else
             nothing
           end)
       end)...))

    # Clear any morphism and data attribute indices for last part.
    $(Expr(:block,
           (map(indexed_out_homs) do hom
              :(set_subpart!(acs, last_part, $(Expr(:quote, hom)), 0))
            end)...))

    for attr in $(Tuple(indexed_attrs))
      if isassigned(subpart(acs, attr), last_part)
        unset_attr_index!(acs.attr_indices[attr], subpart(acs, last_part, attr), last_part)
      end
    end

    # Finally, delete the last part and update subparts of the removed part.
    for f in $(Tuple(out_homs))
      resize!(acs.homs[f], last_part - 1)
    end
    for a in $(Tuple(out_attrs))
      resize!(acs.attrs[a], last_part - 1)
    end
    @inbounds acs.obs[$(ob_num(s, ob))] -= 1
    if part < last_part
      $(Expr(:block,
             (map([out_homs; out_attrs]) do f
                quote
                  x = $(Symbol("last_row_" * string(f)))
                  if !isnothing(x)
                    set_subpart!(acs, part, $(Expr(:quote, f)), x)
                  end
                end
             end)...))
    end
  end
end

@generated function _rem_part!(acs::StructACSet{S,Ts,idxed}, ::Type{Val{ob}},
                               part::Int) where {S,Ts,ob,idxed}
  rem_part_body(SchemaDesc(S),pairs(idxed),ob)
end

function Base.copy(acs::StructACSet)
  new_acs = typeof(acs)()
  ACSetInterface.copy_parts!(new_acs, acs)
  new_acs
end

""" Copy parts from a C-set to a C′-set.

The selected parts must belong to both schemas. All subparts common to the
selected parts, including data attributes, are preserved. Thus, if the selected
parts form a sub-C-set, then the whole sub-C-set is preserved. On the other
hand, if the selected parts do *not* form a sub-C-set, then some copied parts
will have undefined subparts.
"""
@generated function ACSetInterface.copy_parts!(to::StructACSet{S},
                                from::StructACSet{S′}; kw...) where {S, S′}
  s, s′ = SchemaDesc(S), SchemaDesc(S′)
  obs = intersect(s.obs, s′.obs)
  :(copy_parts!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

ACSetInterface.copy_parts!(to::StructACSet, from::StructACSet, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))
ACSetInterface.copy_parts!(to::StructACSet, from::StructACSet, parts::NamedTuple) =
  _copy_parts!(to, from, replace_colons(from, parts))

@generated function _copy_parts!(to::StructACSet{S}, from::StructACSet{S′},
                                 parts::NamedTuple{obs}) where {S, S′, obs}
  s, s′ = SchemaDesc(S), SchemaDesc(S′)
  @assert obs ⊆ intersect(s.obs, s′.obs)
  homs = intersect(s.homs, s′.homs)
  homs = filter(homs) do hom
    c, c′, d, d′ = s.doms[hom], s′.doms[hom], s.codoms[hom], s′.codoms[hom]
    c == c′ && d == d′ && c ∈ obs && d ∈ obs
  end
  hom_triples = [ (hom, s.doms[hom], s.codoms[hom]) for hom in homs ]
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

The selected parts must belong to both schemas. Attributes common to both
schemas are also copied, but no other subparts are copied.

See also: [`copy_parts!`](@ref).
"""
@generated function copy_parts_only!(to::StructACSet{S}, from::StructACSet{S′}; kw...) where
  {S,S′}
  s, s′ = SchemaDesc(S), SchemaDesc(S′)
  obs = intersect(s.obs, s′.obs)
  :(copy_parts_only!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

copy_parts_only!(to::StructACSet, from::StructACSet, obs::Tuple) =
  copy_parts_only!(to, from, NamedTuple{obs}((:) for ob in obs))
copy_parts_only!(to::StructACSet, from::StructACSet, parts::NamedTuple) =
  _copy_parts_only!(to, from, replace_colons(from, parts))

@generated function _copy_parts_only!(to::StructACSet{S}, from::StructACSet{S′},
    parts::NamedTuple{obs}) where {S, S′, obs}
  s, s′ = SchemaDesc(S), SchemaDesc(S′)
  @assert obs ⊆ intersect(s.obs, s′.obs)
  attrs = intersect(s.attrs, s′.attrs)
  attrs = filter(attrs) do attr
    ob, ob′ = s.doms[attr], s′.doms[attr]
    ob == ob′ && ob ∈ obs
  end
  Expr(:block,
    :(newparts = (; $(map(obs) do ob
        Expr(:kw, ob, :(add_parts!(to, $(QuoteNode(ob)), length(parts.$ob))))
        end...))),
    map(attrs) do attr
      ob = s.doms[attr]
      :(set_subpart!(to, newparts.$ob, $(QuoteNode(attr)),
                     subpart(from, parts.$ob, $(QuoteNode(attr)))))
    end...,
    :newparts)
end

function replace_colons(acs::StructACSet, parts::NamedTuple{types}) where {types}
  NamedTuple{types}(map(types, parts) do type, part
    part == (:) ? (1:nparts(acs, type)) : part
  end)
end

# Printing
##########

function Base.show(io::IO, acs::T) where {S,T<:StructACSet{S}}
  s = SchemaDesc(S)
  if get(io, :compact, false)
    print(io, nameof(T))
    print(io, " {")
    join(io, ("$ob = $(nparts(acs,ob))" for ob in s.obs), ", ")
    print(io, "}")
  else
    print(io, T)
    println(io, ":")
    join(io, Iterators.flatten((
      ("  $ob = $(parts(acs,ob))" for ob in s.obs),
      ("  $f : $(s.doms[f]) → $(s.codoms[f]) = $(subpart(acs,f))"
       for f in s.homs),
      ("  $a : $(s.doms[a]) → $(s.codoms[a]) = $(subpart(acs,a))"
       for a in s.attrs),
    )), "\n")
  end
end

# TODO: implement Tables interface
# Steps:
# - Wrapper data structure

struct StructACSetTable{T<:StructACSet, ob} <: Tables.AbstractColumns
  parent::T
end

StructACSetTable(acs::StructACSet, ob::Symbol) = StructACSetTable{typeof(acs), ob}(acs)

ACSetInterface.tables(acs::StructACSet{<:SchemaDescType{obs}}) where {obs} =
  NamedTuple([ob => StructACSetTable(acs, ob) for ob in obs])

parent(sat::StructACSetTable) = getfield(sat, :parent)

struct StructACSetRow{T<:StructACSet, ob} <: Tables.AbstractRow
  parent::T
  idx::Int
end

parent(row::StructACSetRow) = getfield(row, :parent)
idx(row::StructACSetRow) = getfield(row, :idx)

# - Tables.jl interface

Tables.istable(sat::StructACSetTable) = true

Tables.columnaccess(sat::StructACSetTable) = true
Tables.columns(sat::StructACSetTable) = sat

Tables.getcolumn(sat::StructACSetTable{T,ob}, i::Int) where {T,ob} =
  Base.getproperty(sat, outgoing(parent(sat), ob)[i])

Base.getproperty(sat::StructACSetTable, nm::Symbol) = subpart(parent(sat), :, nm)

Tables.getcolumn(sat::StructACSetTable, nm::Symbol) = Base.getproperty(sat, nm)

Base.propertynames(sat::StructACSetTable{T,ob}) where {T,ob} = outgoing(parent(sat), ob)

Tables.columnnames(sat::StructACSetTable) = Base.propertynames(sat)

Tables.rowaccess(sat::StructACSetTable) = true
Tables.rows(sat::StructACSetTable{T,ob}) where {T,ob} =
  StructACSetRow{T,ob}.(Ref(parent(sat)), parts(parent(sat), ob))


Tables.getcolumn(row::StructACSetRow{T,ob}, i::Int) where {T,ob} =
  Base.getproperty(row, outgoing(parent(row), ob)[i])

Base.getproperty(row::StructACSetRow, nm::Symbol) = subpart(parent(row), idx(row), nm)

Tables.getcolumn(row::StructACSetRow, nm::Symbol) = Base.getproperty(row, nm)

Base.propertynames(row::StructACSetRow{T,ob}) where {T,ob} = outgoing(parent(row), ob)

Tables.columnnames(row::StructACSetRow) = Base.propertynames(row)

# Mapping

function Base.map(acs::ACSet; kwargs...)
  _map(acs, (;kwargs...))
end

function sortunique!(x)
  sort!(x)
  unique!(x)
  x
end

function groupby(f::Function, xs)
  d = Dict{typeof(f(xs[1])),Vector{eltype(xs)}}()
  for x in xs
    k = f(x)
    if k in keys(d)
      push!(d[k],x)
    else
      d[k] = [x]
    end
  end
  d
end

@generated function _map(acs::AT, fns::NamedTuple{map_over}) where
  {S, Ts, AT<:StructACSet{S,Ts}, map_over}
  s = SchemaDesc(S)
  map_over = Symbol[map_over...]

  mapped_attrs = intersect(s.attrs, map_over)
  mapped_attrtypes = intersect(s.attrtypes, map_over)
  mapped_attrs_from_attrtypes = filter(a -> s.codoms[a] ∈ mapped_attrtypes, s.attrs)
  attrs_accounted_for = sortunique!(Symbol[mapped_attrs; mapped_attrs_from_attrtypes])

  affected_attrtypes = sortunique!(map(a -> s.codoms[a], attrs_accounted_for))
  needed_attrs = sort!(filter(a -> s.codoms[a] ∈ affected_attrtypes, s.attrs))

  unnaccounted_for_attrs = filter(a -> a ∉ attrs_accounted_for, needed_attrs)
  unnaccounted_for_attrs == [] ||
    error("not enough functions provided to fully transform ACSet, need functions for: $(unnaccounted_for_attrs)")

  fn_applications = map(attrs_accounted_for) do a
    qa = q(a)
    if a ∈ mapped_attrs
      :($a = (fns[$qa]).(subpart(acs, $qa)))
    else
      d = s.codoms[a]
      :($a = (fns[$(q(d))]).(subpart(acs, $qa)))
    end
  end

  abc = groupby(a -> s.codoms[a], s.attrs)

  attrtype_instantiations = map(enumerate(s.attrtypes)) do (i,d)
    if d ∈ affected_attrtypes
      :(mapreduce(eltype, typejoin,
                  $(Expr(:tuple, (:(fn_vals[$(q(a))]) for a in abc[d])...))))
    else
      :($(Ts[i]))
    end
  end

  quote
    fn_vals = $(Expr(:tuple, fn_applications...))
    new_acs = $(AT.name.wrapper){$(attrtype_instantiations...)}()
    $(Expr(:block, map(s.obs) do ob
           :(add_parts!(new_acs,$(q(ob)),nparts(acs,$(q(ob)))))
      end...))
    $(Expr(:block, map(s.homs) do hom
           :(set_subpart!(new_acs,$(q(hom)),subpart(acs,$(q(hom)))))
      end...))
    $(Expr(:block, map(s.attrs) do attr
        qa = Expr(:quote, attr)
        if attr ∈ attrs_accounted_for
           :(set_subpart!(new_acs,$qa,fn_vals[$qa]))
        else
           :(set_subpart!(new_acs,$qa,subpart(acs,$qa)))
        end
      end...))
    return new_acs
  end
end

end

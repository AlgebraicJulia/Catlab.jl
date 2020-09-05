module CSets
export AbstractACSet, ACSet, AbstractCSet, CSet,
  AbstractACSetType, ACSetType, AbstractCSetType, CSetType,
  nparts, has_part, subpart, has_subpart, incident, add_part!, add_parts!,
  copy_parts!, set_subpart!, set_subparts!, disjoint_union

# Compatibility with Julia v1.0.
import Base: fieldnames
if VERSION < v"1.1"
  fieldtypes(::Type{T}) where T <: NamedTuple = T.parameters[2].parameters
  fieldtypes(::Type) = ()
else
  import Base: fieldtypes
end

using Compat: isnothing
using StructArrays

using ...Theories
using ...Present

# Struct arrays
###############

const EmptyTuple = Union{Tuple{},NamedTuple{(),Tuple{}}}
const StructArray0{T} = Union{StructArray{T},Vector{<:EmptyTuple}}

""" Create StructArray while avoiding inconsistency with zero length arrays.

By default, just constructs a StructArray (a struct of arrays) but when struct
is empty, returns a ordinary Julia vector (an array of empty structs).

See: https://github.com/JuliaArrays/StructArrays.jl/issues/148
"""
make_struct_array(x) = StructArray(x)

function make_struct_array(n::Int, x)
  sa = StructArray(x)
  @assert length(sa) == n
  sa
end

make_struct_array(::EmptyTuple) = error("Length needed when struct is empty")
make_struct_array(n::Int, ::T) where T <: EmptyTuple = fill(T(()), n)
make_struct_array(v::Vector{<:EmptyTuple}) = v

make_struct_array(::Type{SA}, ::UndefInitializer, n::Int) where
  SA <: StructArray = SA(undef, n)
make_struct_array(::Type{<:StructArray{T}}, ::UndefInitializer, n::Int) where
  T <: EmptyTuple = fill(T(()), n)

function fieldtypes(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fieldtypes(eltype(T))
end
function fieldnames(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fieldnames(eltype(T))
end

# Data types
############

abstract type AbstractAttributedCSet{CD,AD,Ts} end

const AbstractACSet = AbstractAttributedCSet

struct AttributedCSet{CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed,
             TablesType <: NamedTuple, IndicesType <: NamedTuple} <: AbstractACSet{CD,AD,Ts}
  tables::TablesType
  indices::IndicesType
  function AttributedCSet{CD,AD,Ts,Idxed}() where {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed}
    tables = make_tables(CD,AD,Ts)
    indices = make_indices(CD,AD,Ts,Idxed)
    new{CD,AD,Ts,Idxed,typeof(tables),typeof(indices)}(tables,indices)
  end
  function AttributedCSet{CD}() where {CD <: CatDesc}
    AttributedCSet{CD,typeof(AttrDesc(CD())),Tuple{}}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed,TT,IT}() where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    AttributedCSet{CD,AD,Ts,Idxed}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed,TT,IT}(tables::TT,indices::IT) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    new{CD,AD,Ts,Idxed,TT,IT}(tables,indices)
  end
end

const ACSet = AttributedCSet

function AbstractACSetType(pres::Presentation{Schema})
  ACSet{CatDescType(pres)}
end

function ACSetType(pres::Presentation{Schema}; index=[])
  ty_params = [TypeVar(nameof(data_type)) for data_type in generators(pres,:Data)]
  foldr((v,T) -> UnionAll(v,T), ty_params,
        init=ACSet{SchemaType(pres)...,Tuple{ty_params...},Tuple(index)})
end

const AbstractCSet{CD} = AbstractACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{}}
const CSet{CD,Idxed} = ACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{},Idxed}

function AbstractCSetType(pres::Presentation{Schema})
  AbstractCSet{CatDescType(pres)}
end

function CSetType(pres::Presentation{Schema}; index=[])
  CSet{CatDescType(pres),Tuple(index)}
end

function make_indices(::Type{CD},AD::Type{<:AttrDesc{CD}},Ts::Type{<:Tuple},Idxed::Tuple) where {CD}
  ts = Ts.parameters
  function make_idx(name)
    if name ∈ CD.hom
      Vector{Vector{Int}}()
    elseif name ∈ AD.attr
      Dict{ts[codom_num(AD,name)],Vector{Int}}()
    else
      error("Cannot index $name: not a morphism or an attribute")
    end
  end
  NamedTuple{Idxed}(Tuple(make_idx(name) for name in Idxed))
end

function make_tables(::Type{CD}, AD::Type{<:AttrDesc{CD}}, Ts::Type{<:Tuple}) where {CD}
  ts = Ts.parameters
  cols = NamedTuple{CD.ob}(Tuple{Symbol,DataType}[] for ob in CD.ob)
  for hom in CD.hom
    push!(cols[dom(CD,hom)], (hom,Int))
  end
  for attr in AD.attr
    push!(cols[dom(AD,attr)], (attr,ts[codom_num(AD,attr)]))
  end
  map(cols) do col
    SA = StructArray{NamedTuple{Tuple(first.(col)),Tuple{last.(col)...}}}
    make_struct_array(SA, undef, 0)
  end
end

function Base.:(==)(x1::T, x2::T) where T <: ACSet
  x1.tables == x2.tables
end

function Base.copy(acs::T) where T <: ACSet
  T(map(copy, acs.tables),map(copy, acs.indices))
end

Base.empty(acs::T) where T <: ACSet = T()

nparts(acs::ACSet,type::Symbol) = length(acs.tables[type])

has_part(acs::ACSet, type::Symbol, part::Int) = 1 <= part <= nparts(acs,type)
has_part(acs::ACSet, type::Symbol, part::AbstractVector{Int}) =
  let n=nparts(acs, type); [ 1 <= x <= n for x in part ] end

has_part(acs::ACSet,type::Symbol) = _has_part(acs, Val(type))

@generated function _has_part(::ACSet{CD,AD}, ::Val{type}) where {CD,AD,type}
  type ∈ CD.ob || type ∈ AD.data
end

""" Whether a C-set has a subpart with the given name.
"""
has_subpart(acs::ACSet, name::Symbol) = _has_subpart(acs, Val(name))

@generated function _has_subpart(::ACSet{CD,AD}, ::Val{name}) where {CD,AD,name}
  name ∈ CD.hom || name ∈ AD.attr
end

subpart(acs::ACSet, part, name::Symbol) = subpart(acs,name)[part]
subpart(acs::ACSet, name::Symbol) = _subpart(acs,Val(name))

@generated function _subpart(acs::ACSet{CD,AD,Ts},::Val{name}) where {CD,AD,Ts,name}
  if name ∈ CD.hom
    :(acs.tables.$(dom(CD,name)).$name)
  elseif name ∈ AD.attr
    :(acs.tables.$(dom(AD,name)).$name)
  else
    throw(KeyError(name))
  end
end

function Base.show(io::IO, acs::AbstractACSet{CD,AD,Ts}) where {CD,AD,Ts}
  println(io,"ACSet")
  for ob in CD.ob
    println(io, "  $ob = 1:$(nparts(acs,ob))")
  end
  for (i,hom) in enumerate(CD.hom)
    println(io, "  $hom : $(dom(CD,i)) → $(codom(CD,i))")
    println(io, "    $(subpart(acs,hom))")
  end
  for (i,conc) in enumerate(AD.data)
    println(io, "  $conc = $(Ts.parameters[i])")
  end
  for (i,attr) in enumerate(AD.attr)
    println(io, "  $attr : $(dom(AD,i)) ⇒ $(codom(AD,i))")
    println(io, "    $(subpart(acs,attr))")
  end
end

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  @assert i <= length(a) && a[i] == x "Value $x is not contained in $a"
  deleteat!(a, i)
end

add_part!(acs::ACSet, type::Symbol, subparts::NamedTuple) =
  _add_parts!(acs, Val(type), make_struct_array([subparts]))[1]
add_part!(acs::ACSet, type::Symbol; kw...) = add_part!(acs, type, (; kw...))

add_parts!(acs::ACSet, type::Symbol, subpartses::StructArray0{<:NamedTuple}) =
  _add_parts!(acs, Val(type), subpartses)
add_parts!(acs::ACSet, type::Symbol; kw...) =
  add_parts!(acs, type, make_struct_array((; kw...)))
add_parts!(acs::ACSet,type::Symbol, n::Int; kw...) =
  add_parts!(acs, type, make_struct_array(n, (; kw...)))

@generated function _add_parts!(acs::ACSet{CD,AD,Ts,Idxed,TT},::Val{ob},
                                subpartses::T) where
  {CD,AD,Ts,Idxed,TT,ob,T<:StructArray0{<:NamedTuple}}
  @assert fieldnames(T) == fieldnames(fieldtype(TT,ob))
  @assert fieldtypes(T) == fieldtypes(fieldtype(TT,ob))
  code = quote
    append!(acs.tables.$ob,subpartses)
  end
  for (i,hom) in enumerate(CD.hom)
    if hom ∈ Idxed && CD.ob[CD.codom[i]] == ob
      push!(code.args, :(append!(acs.indices.$(hom), repeat([[]],length(subpartses)))))
    end
  end
  inner_loop = Expr(:block)
  for hom in fieldnames(T)
    if hom ∈ Idxed
      if hom ∈ CD.hom
        indices_code = quote
          if has_part(acs, $(Expr(:quote, codom(CD,hom))), subparts.$hom)
            insertsorted!(acs.indices.$(hom)[subparts.$hom],part_num)
          elseif subparts.$hom != 0
            error("No part $(subparts.$hom) exists of type $($(Expr(:quote, codom(CD,hom))))")
          end
        end
        push!(inner_loop.args, indices_code)
      elseif hom ∈ AD.attr
        indices_code = quote
          if subparts.$hom ∈ keys(acs.indices.$hom)
            insertsorted!(acs.indices.$(hom)[subparts.$hom],part_num)
          else
            acs.indices.$(hom)[subparts.$hom] = [part_num]
          end
        end
        push!(inner_loop.args, indices_code)
      end
    end
  end
  quote
    k = length(subpartses)
    n = nparts(acs,ob)
    $code
    for (i,subparts) in enumerate(subpartses)
      part_num = i+n
      $inner_loop
    end
    (n+1):(n+k)
  end
end

incident(acs::ACSet, part, name::Symbol) = _incident(acs, part, Val(name))

get_data_index(d::AbstractDict{K,Int}, k::K) where K =
  get(d, k, nothing)
get_data_index(d::AbstractDict{K,<:AbstractVector{Int}}, k::K) where K =
  get(d, k, 1:0)

@generated function _incident(acs::ACSet{CD,AD,Ts,Idxed}, part, ::Val{name}) where {CD,AD,Ts,Idxed,name}
  if name ∈ Idxed
    if name ∈ CD.hom
      :(acs.indices.$name[part])
    else
      :(get_data_index.(Ref(acs.indices.$name),part))
    end
  else
    throw(KeyError(name))
  end
end

@generated function _set_subpart!(acs::ACSet{CD,AD,Ts,Idxed}, part::Int, ::Val{name}, subpart) where
  {CD,AD,Ts,Idxed,name}
  code = Expr(:block)
  if name ∈ CD.hom
    push!(code.args, quote
          old = acs.tables.$(dom(CD,name)).$(name)[part]
          acs.tables.$(dom(CD,name)).$name[part] = subpart
          end)
  elseif name ∈ AD.attr
    push!(code.args, quote
          old = acs.tables.$(dom(AD,name)).$(name)[part]
          acs.tables.$(dom(AD,name)).$name[part] = subpart
          end)
  else
    throw(KeyError(name))
  end
  if name ∈ Idxed
    if name ∈ CD.hom
      indices_code = quote
        @assert has_part(acs,$(Expr(:quote, codom(CD,name))),subpart)
        if old != 0
          deletesorted!(acs.indices.$(name)[old], part)
        end
        insertsorted!(acs.indices.$(name)[subpart], part)
      end
      push!(code.args, indices_code)
    elseif name ∈ AD.attr
      indices_code = quote
        @assert pop!(acs.indices.$name, old) == part
        insertsorted!(get!(acs.indices.$name, subpart) do; Int[] end, part)
      end
      push!(code.args, indices_code)
    end
  end
  code
end

set_subpart!(acs::ACSet, part::Int, name, subpart) = _set_subpart!(acs, part, Val(name), subpart)

function set_subpart!(acs::ACSet, parts::AbstractArray{Int}, name, subparts::AbstractArray)
  for (part,subpart) in zip(parts,subparts)
    set_subpart!(acs,part,name,subpart)
  end
end

## FIXME: Put a more specific type on this
function set_subpart!(acs::ACSet, parts::AbstractArray{Int}, name, subpart)
  for part in parts
    set_subpart!(acs,part,name,subpart)
  end
end

function set_subpart!(acs::ACSet{CD,AD}, parts::Colon, name, subparts) where {CD,AD}
  part_type = if name ∈ CD.hom
    dom(CD,name)
  elseif name ∈ AD.attr
    dom(AD,name)
  else
    error("No such subpart: $name")
  end
  set_subpart!(acs,1:nparts(acs,part_type),name,subparts)
end

function set_subparts!(acs::ACSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(acs, part, name, subpart)
  end
end

""" Copy parts from one C-set into another.
All subparts among the selected parts, including any attached data, are
preserved. Thus, if the selected parts form a sub-C-set, then the whole
sub-C-set is preserved. On the other hand, if the selected parts do *not* form a
sub-C-set, then some copied parts will have undefined subparts.
"""
copy_parts!(acs::ACSet, from::ACSet; kw...) =
  copy_parts!(acs, from, (; kw...))
copy_parts!(acs::ACSet, from::ACSet, type::Symbol) =
  copy_parts!(acs, from, (; type => :))
copy_parts!(acs::ACSet, from::ACSet, type::Symbol, parts) =
  copy_parts!(acs, from, (; type => parts))
copy_parts!(acs::ACSet, from::ACSet, types::Tuple) =
  copy_parts!(acs::ACSet, from::ACSet, NamedTuple{types}((:) for t in types))

function copy_parts!(acs::ACSet, from::ACSet, parts::NamedTuple{types}) where types
  parts = map(types, parts) do type, part
    part == (:) ? (1:nparts(from, type)) : part
  end
  _copy_parts!(acs, from, NamedTuple{types}(parts))
end

@generated function _copy_parts!(acs::T, from::T, parts::NamedTuple{types}) where
    {types,CD,AD,Ts,Idx,T <: ACSet{CD,AD,Ts,Idx}}
  obnums = ob_num.(CD, types)
  in_obs, out_homs = Symbol[], Tuple{Symbol,Symbol,Symbol}[]
  for (hom, dom, codom) in zip(CD.hom, CD.dom, CD.codom)
    if dom ∈ obnums && codom ∈ obnums
      push!(in_obs, CD.ob[codom])
      push!(out_homs, (hom, CD.ob[dom], CD.ob[codom]))
    end
  end
  in_obs = Tuple(unique!(in_obs))
  quote
    newparts = NamedTuple{$types}(tuple($(map(types) do type
      :(_copy_parts_data!(acs, from, Val($(QuoteNode(type))), parts.$type))
    end...)))
    partmaps = NamedTuple{$in_obs}(tuple($(map(in_obs) do type
      :(Dict{Int,Int}(zip(parts.$type, newparts.$type)))
    end...)))
    for (name, dom, codom) in $(Tuple(out_homs))
      for (p, newp) in zip(parts[dom], newparts[dom])
        q = subpart(from, p, name)
        newq = get(partmaps[codom], q, nothing)
        if !isnothing(newq)
          set_subpart!(acs, newp, name, newq)
        end
      end
    end
    newparts
  end
end

@generated function _copy_parts_data!(acs::T, from::T, ::Val{type}, parts) where
  {type,CD,AD,T<:ACSet{CD,AD}}
  homs = collect(filter(hom -> dom(CD,hom) == type, CD.hom))
  attrs = collect(filter(attr -> dom(AD,attr) == type, AD.attr))
  subparts = [[Expr(:kw, hom, :(zeros(Int64,n))) for hom in homs];
              [Expr(:kw, attr, :(subpart(from,parts,$(Expr(:quote, attr))))) for attr in attrs]]
  quote
    n = length(parts)
    $(Expr(:call, :add_parts!, Expr(:parameters, subparts...), :acs, Expr(:quote, type), :n))
  end
end

function disjoint_union(acs1::T,acs2::T) where {CD,AD,T<:ACSet{CD,AD}}
  acs = copy(acs1)
  copy_parts!(acs,acs2,CD.ob)
  acs
end

end

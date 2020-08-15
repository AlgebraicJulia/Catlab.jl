module ACSets
export AbstractACSet, ACSet, AbstractCSet, CSet,
  nparts, has_part, subpart, has_subpart, incident, add_part!, add_parts!,
  copy_parts!, set_subpart!, set_subparts!, disjoint_union

using ...Theories

# FIXME: We use a monkey-patched StructArray to get around
# https://github.com/JuliaArrays/StructArrays.jl/issues/148

include("StructArrayWithLength.jl")

abstract type AbstractACSet{CD,AD,Ts} end

struct ACSet{CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed,
             TablesType <: NamedTuple, IndicesType <: NamedTuple} <: AbstractACSet{CD,AD,Ts}
  tables::TablesType
  indices::IndicesType
  function ACSet{CD,AD,Ts,Idxed}() where {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed}
    tables = make_tables(CD,AD,Ts)
    indices = make_indices(CD,AD,Ts,Idxed)
    new{CD,AD,Ts,Idxed,typeof(tables),typeof(indices)}(tables,indices)
  end
  function ACSet{CD}() where {CD <: CatDesc}
    ACSet{CD,typeof(AttrDesc(CD())),Tuple{}}()
  end
  function ACSet{CD,AD,Ts,Idxed,TT,IT}() where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    ACSet{CD,AD,Ts,Idxed}()
  end
  function ACSet{CD,AD,Ts,Idxed,TT,IT}(tables::TT,indices::IT) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    new{CD,AD,Ts,Idxed,TT,IT}(tables,indices)
  end
end

const AbstractCSet{CD} = AbstractACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{}}
const CSet{CD,Idxed} = ACSet{CD,AttrDesc{CD,(),(),(),()},Tuple{},Idxed}

function make_indices(::Type{CD},AD::Type{<:AttrDesc{CD}},Ts::Type{<:Tuple},Idxed::Tuple) where {CD}
  ts = Ts.parameters
  function make_idx(name)
    if name ∈ CD.hom
      Vector{Vector{Int}}()
    elseif name ∈ AD.attr
      Dict{ts[codom_num(AD,name)],Vector{Int}}()
    else
      error("invalid indices parameter")
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
  map(col -> StructArrayWithLength{NamedTuple{Tuple(first.(col)),Tuple{last.(col)...}}}(undef,0), cols)
end

function Base.fieldnames(::Type{T}) where {T <: StructArrayWithLength{<:NamedTuple}}
  fieldnames(eltype(T))
end

function Base.fieldtypes(::Type{T}) where {T <: StructArrayWithLength{<:NamedTuple}}
  fieldtypes(eltype(T))
end

function Base.:(==)(x1::T, x2::T) where T <: ACSet
  x1.tables == x2.tables
end

function Base.copy(acs::T) where T <: ACSet
  T(copy(acs.tables),copy(acs.indices))
end

Base.empty(acs::T) where T <: ACSet = T()

nparts(acs::ACSet,type::Symbol) = length(acs.tables[type])

has_part(acs::ACSet,type::Symbol,part::Int) = 1 <= part <= nparts(acs,type)

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

function Base.show(io::IO, ::MIME"text/plain", acs::AbstractACSet{CD,AD,Ts}) where {CD,AD,Ts}
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

add_part!(acs::ACSet,type::Symbol,subparts::NamedTuple) =
  _add_parts!(acs,Val(type),StructArrayWithLength([subparts]))[1]
add_part!(acs::ACSet,type::Symbol;kwargs...) = add_part!(acs,type,(;kwargs...))

add_parts!(acs::ACSet,type::Symbol,subpartses::StructArrayWithLength{<:NamedTuple}) =
  _add_parts!(acs,Val(type),subpartses)
add_parts!(acs::ACSet,type::Symbol;kwargs...) = add_parts!(acs,type,StructArrayWithLength(;kwargs...))
add_parts!(acs::ACSet,type::Symbol,n::Int;kwargs...) = add_parts!(acs,type,StructArrayWithLength(n;kwargs...))

@generated function _add_parts!(acs::ACSet{CD,AD,Ts,Idxed,TT},::Val{ob},
                                subpartses::T) where
  {CD,AD,Ts,Idxed,TT,ob,T<:StructArrayWithLength{<:NamedTuple}}
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
          @assert has_part(acs, $(Expr(:quote, codom(CD,hom))), subparts.$hom)
          insertsorted!(acs.indices.$(hom)[subparts.$hom],part_num)
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
        deletesorted!(acs.indices.$(name)[old], part)
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

set_subpart!(acs::ACSet, part, name, subpart) = _set_subpart!(acs, part, Val(name), subpart)

function set_subparts!(acs::ACSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(acs, part, name, subpart)
  end
end

end

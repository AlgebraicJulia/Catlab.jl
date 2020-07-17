""" Generic data structures for C-sets (presheaves).
"""
module CSets
export AbstractCSet, AbstractCSetType, CSet, CSetType,
  nparts, has_part, subpart, has_subpart, incident,
  add_part!, add_parts!, copy_parts!, set_subpart!, set_subparts!

using Compat
using LabelledArrays, StaticArrays

using ...Present
using ...Theories: Category, dom, codom

# C-set data types
##################

const NamedSVector{Names,T,N} = SLArray{Tuple{N},T,1,N,Names}

""" Abstract type for C-sets (presheaves).

The type parameters are:
- `Ob`: tuple of symbols naming objects
- `Hom`: tuple of symbols naming morphims
- `Dom`: tuple of integers giving domain of each morphism
- `Codom`: tuple of integers giving codomain of each morphism
- `Data`: tuple of symbols naming extra morphisms for data/attributes
- `DataDom`: tuple of integers giving domain of each data morphism

For example, a graph with one vertex attribute could be represented as
`AbstractCSet{(:V,:E),(:src,:tgt),(2,2),(1,1),(:vattr,),(1,)}`.

See also: [`CSet`](@ref) and [`CSetType`](@ref).
"""
abstract type AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom} end

""" Data type for C-sets (presheaves).

Instead of filling out the type parameters manually, we recommend using the
function [`CSetType`](@ref) to generate a `CSet` type from a presentation of a
category. Nevertheless, the first six type parameters are documented at
[`AbstractCSet`](@ref). The remaining type parameters are an implementation
detail and should be ignored.

Following LightGraphs.jl, the incidence vectors, stored in the `incidence`
field, are kept in sorted order. To ensure consistency, no field of the struct
should ever be mutated directly.
"""
mutable struct CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique} <:
       AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom}
  nparts::NamedSVector{Ob,Int}
  subparts::NamedSVector{Hom,Vector{Int}}
  indices::NamedSVector{Index,Vector{Vector{Int}}}
  data::NamedTuple{Data}
  data_indices::NamedTuple{DataIndex}
end

function CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}(;
    kw...) where {Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}((; kw...))
end
function CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}(
    datatypes::NamedTuple{Data}) where
    {Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}
  NOb, NHom, NIndex = length(Ob), length(Hom), length(Index)
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,DataIndex,IsUnique}(
    NamedSVector{Ob,Int,NOb}(zeros(SVector{NOb,Int})),
    NamedSVector{Hom,Vector{Int},NHom}(Tuple(Int[] for i in 1:NHom)),
    NamedSVector{Index,Vector{Vector{Int}},NIndex}(
      Tuple(Vector{Int}[] for i in 1:NIndex)),
    NamedTuple{Data}(Union{T,Missing}[] for T in datatypes),
    NamedTuple{DataIndex}(
      Dict{datatypes[name], is_unique ? Int : Vector{Int}}()
      for (name, is_unique) in zip(DataIndex, IsUnique)))
end

""" Generate an abstract C-set type from a presentation of a category.

See also: [`CSetType`](@ref).
"""
function AbstractCSetType(pres::Presentation{Category}; data=())
  # Only include `Data` and `DataDom` params if there are data morphisms.
  Ts = CSetTypeParams(pres, data=data)
  AbstractCSet{(isempty(Ts[5]) ? Ts[1:4] : Ts[1:6])...}
end

""" Generate a C-set data type from a presentation of a category.

See also: [`AbstractCSetType`](@ref).
"""
function CSetType(pres::Presentation{Category}; kw...)
  CSet{CSetTypeParams(pres; kw...)...}
end

function CSetTypeParams(pres::Presentation{Category};
                        data=(), index=(), unique_index=())
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  data_obs, obs = separate(ob -> nameof(ob) ∈ data, obs)
  data_homs, homs = separate(hom -> codom(hom) ∈ data_obs, homs)
  data_index, index = separate(name -> name ∈ nameof.(data_homs),
                               sort!(index ∪ unique_index))
  ob_num = ob -> findfirst(obs .== ob)::Int
  (Tuple(nameof.(obs)), Tuple(nameof.(homs)),
   Tuple(@. ob_num(dom(homs))), Tuple(@. ob_num(codom(homs))),
   Tuple(nameof.(data_homs)), Tuple(@. ob_num(dom(data_homs))),
   Tuple(index), Tuple(data_index), Tuple(k ∈ unique_index for k in data_index))
end
separate(f, a::AbstractArray) = (i = f.(a); (a[i], a[.!i]))

function Base.:(==)(x1::T, x2::T) where T <: CSet
  # The subpart and data indices are redundant, so need not be compared.
  x1.nparts == x2.nparts && x1.subparts == x2.subparts && x1.data == x2.data
end

function Base.copy(cset::T) where T <: CSet
  T(cset.nparts, map(copy, cset.subparts), map(copy, cset.indices),
    map(copy, cset.data), map(copy, cset.data_indices))
end

Base.empty(cset::T) where T <: CSet = T(map(eltype, cset.data))

# C-set interface
#################

""" Number of parts of given type in a C-set.
"""
nparts(cset::CSet, type::Symbol) = cset.nparts[type]

""" Whether a C-set has a part with the given name.
"""
has_part(cset::CSet, type::Symbol) = _has_part(cset, Val(type))

@generated _has_part(cset::CSet{obs}, ::Val{type}) where {obs,type} =
  type ∈ obs

has_part(cset::CSet, type::Symbol, part::Int) = 1 <= part <= nparts(cset, type)
has_part(cset::CSet, type::Symbol, part::AbstractVector{Int}) =
  let n=nparts(cset, type); [ 1 <= x <= n for x in part ] end

""" Get subpart of part in C-set.

Both single and vectorized access are supported.
"""
subpart(cset::CSet, part, name::Symbol) = subpart(cset, name)[part]
subpart(cset::CSet, name::Symbol) = _subpart(cset, Val(name))

@generated function _subpart(cset::T, ::Val{name}) where
    {name, obs,homs,doms,codoms,data, T <: CSet{obs,homs,doms,codoms,data}}
  if name ∈ homs
    :(cset.subparts.$name)
  elseif name ∈ data
    :(cset.data.$name)
  else
    throw(KeyError(name))
  end
end

""" Whether a C-set has a subpart with the given name.
"""
has_subpart(cset::CSet, name::Symbol) = _has_subpart(cset, Val(name))

@generated function _has_subpart(cset::T, ::Val{name}) where
    {name, obs,homs,doms,codoms,data, T <: CSet{obs,homs,doms,codoms,data}}
  name ∈ homs || name ∈ data
end

""" Get superparts incident to part in C-set.
"""
incident(cset::CSet, part, name::Symbol) = _incident(cset, part, Val(name))

@generated function _incident(cset::T, part, ::Val{name}) where
    {name, obs,homs,doms,codoms,data,data_doms,indexed,data_indexed,
     T <: CSet{obs,homs,doms,codoms,data,data_doms,indexed,data_indexed}}
  if name ∈ indexed
    :(cset.indices.$name[part])
  elseif name ∈ data_indexed
    :(get_data_index.(Ref(cset.data_indices.$name), part))
  else
    throw(KeyError(name))
  end
end

""" Add part of given type to C-set, optionally setting its subparts.

Returns the ID of the added part.

See also: [`add_parts!`](@ref).
"""
function add_part!(cset::CSet, type::Symbol, args...; kw...)
  part = only(_add_parts!(cset, Val(type), 1))
  set_subparts!(cset, part, args...; kw...)
  part
end

""" Add parts of given type to C-set, optionally setting their subparts.

Returns the range of IDs for the added parts.

See also: [`add_part!`](@ref).
"""
function add_parts!(cset::CSet, type::Symbol, n::Int, args...; kw...)
  parts = _add_parts!(cset, Val(type), n)
  set_subparts!(cset, parts, args...; kw...)
  parts
end

@generated function _add_parts!(cset::T, ::Val{type}, n::Int) where
    {type, obs,homs,doms,codoms,data,data_doms,indexed,
     T <: CSet{obs,homs,doms,codoms,data,data_doms,indexed}}
  ob_num = findfirst(obs .== type)::Int
  in_homs = [ homs[i] for (i, codom) in enumerate(codoms) if codom == ob_num ]
  out_homs = [ homs[i] for (i, dom) in enumerate(doms) if dom == ob_num ]
  data_homs = [ data[i] for (i, dom) in enumerate(data_doms) if dom == ob_num ]
  indexed_homs = filter(hom -> hom ∈ indexed, in_homs)
  # Question: The three loops could (should?) be unrolled. Or is the Julia
  # compiler smart enough to do this on its own?
  quote
    if n == 0; return 1:0 end
    nparts = cset.nparts.$type + n
    cset.nparts = SLVector(cset.nparts; $type=nparts)
    start = nparts - n + 1
    for name in $(Tuple(out_homs))
      resize!(cset.subparts[name], nparts)
      @inbounds cset.subparts[name][start:nparts] .= 0
    end
    for name in $(Tuple(indexed_homs))
      index = cset.indices[name]
      resize!(index, nparts)
      @inbounds for part in start:nparts; index[part] = Int[] end
    end
    for name in $(Tuple(data_homs))
      resize!(cset.data[name], nparts)
      @inbounds cset.data[name][start:nparts] .= missing
    end
    start:nparts
  end
end

""" Copy parts from one C-set to another.

All subparts between the selected parts, including any attached data, are
preserved. Thus, if the selected parts form a sub-C-set, then the whole
sub-C-set is preserved. On the other hand, if the selected parts do *not* form a
sub-C-set, then some copied parts will have undefined subparts.
"""
copy_parts!(cset::CSet, from::CSet; kw...) = copy_parts!(cset, from, (; kw...))

copy_parts!(cset::CSet, from::CSet, type::Symbol, parts) =
  copy_parts!(cset, from, (; type => parts))

@generated function copy_parts!(cset::T, from::T, parts::NamedTuple{types}) where
    {types, obs,homs,doms,codoms, T <: CSet{obs,homs,doms,codoms}}
  obnums = [ findfirst(obs .== type)::Int for type in types ]
  in_obs, out_homs = Symbol[], Tuple{Symbol,Symbol,Symbol}[]
  for (hom, dom, codom) in zip(homs, doms, codoms)
    if dom ∈ obnums && codom ∈ obnums
      push!(in_obs, obs[codom])
      push!(out_homs, (hom, obs[dom], obs[codom]))
    end
  end
  in_obs = Tuple(unique!(in_obs))
  quote
    newparts = NamedTuple{$types}(tuple($(map(types) do type
      :(_copy_parts_data!(cset, from, Val($(QuoteNode(type))), parts.$type))
    end...)))
    partmaps = NamedTuple{$in_obs}(tuple($(map(in_obs) do type
      :(Dict{Int,Int}(zip(parts.$type, newparts.$type)))
    end...)))
    for (name, dom, codom) in $(Tuple(out_homs))
      for (p, newp) in zip(parts[dom], newparts[dom])
        q = subpart(from, p, name)
        newq = get(partmaps[codom], q, nothing)
        if !isnothing(newq)
          set_subpart!(cset, newp, name, newq)
        end
      end
    end
    newparts
  end
end

""" Copy parts of a single type from one C-set to another.

Any data attached to the parts is also copied.
"""
@generated function _copy_parts_data!(cset::T, from::T, ::Val{type}, parts) where
    {type, obs,homs,doms,codoms,data,data_doms,
     T <: CSet{obs,homs,doms,codoms,data,data_doms}}
  obnum = findfirst(obs .== type)::Int
  data_homs = [ data[i] for (i, dom) in enumerate(data_doms) if dom == obnum ]
  quote
    newparts = add_parts!(cset, $(QuoteNode(type)), length(parts))
    for name in $(Tuple(data_homs))
      set_subpart!(cset, newparts, name, from.data[name][parts])
    end
    newparts
  end
end

""" Mutate subpart of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subparts!`](@ref).
"""
set_subpart!(cset::CSet, part::Int, name::Symbol, subpart) =
  _set_subpart!(cset, part, Val(name), subpart)

function set_subpart!(cset::CSet, part::AbstractVector{Int},
                      name::Symbol, subpart)
  broadcast(part, subpart) do part, subpart
    _set_subpart!(cset, part, Val(name), subpart)
  end
end

set_subpart!(cset::CSet, ::Colon, name::Symbol, subpart) =
  set_subpart!(cset, name, subpart)
set_subpart!(cset::CSet, name::Symbol, new_subpart) =
  set_subpart!(cset, 1:length(subpart(cset, name)), name, new_subpart)

@generated function _set_subpart!(cset::T, part::Int, ::Val{name}, subpart) where
    {name, obs,homs,doms,codoms,data,data_doms,indexed,data_indexed,
     T <: CSet{obs,homs,doms,codoms,data,data_doms,indexed,data_indexed}}
  if name ∈ homs
    codom = obs[codoms[findfirst(name .== homs)]]
  end
  if name ∈ indexed
    quote
      @assert 0 <= subpart <= cset.nparts.$codom
      old = cset.subparts.$name[part]
      cset.subparts.$name[part] = subpart
      if old > 0
        deletesorted!(cset.indices.$name[old], part)
      end
      if subpart > 0
        insertsorted!(cset.indices.$name[subpart], part)
      end
    end
  elseif name ∈ homs
    quote
      @assert 0 <= subpart <= cset.nparts.$codom
      cset.subparts.$name[part] = subpart
    end
  elseif name ∈ data_indexed
    quote
      old = cset.data.$name[part]
      cset.data.$name[part] = subpart
      if !ismissing(old)
        unset_data_index!(cset.data_indices.$name, old, part)
      end
      if !ismissing(subpart)
        set_data_index!(cset.data_indices.$name, subpart, part)
      end
    end
  elseif name ∈ data
    :(cset.data.$name[part] = subpart)
  else
    throw(KeyError(name))
  end
end

""" Mutate subparts of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subpart!`](@ref).
"""
set_subparts!(cset::CSet, part; kw...) = set_subparts!(cset, part, (; kw...))

function set_subparts!(cset::CSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(cset, part, name, subpart)
  end
end

""" Look up key in C-set data index.
"""
get_data_index(d::AbstractDict{K,Int}, k::K) where K =
  get(d, k, nothing)
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

""" Unset key and value from C-set data index.
"""
function unset_data_index!(d::AbstractDict{K,Int}, k::K, v::Int) where K
  @assert pop!(d, k) == v
end
function unset_data_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                           k::K, v::Int) where K
  vs = d[k]
  deletesorted!(vs, v)
  if isempty(vs)
    delete!(d, k)
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

end

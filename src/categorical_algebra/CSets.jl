""" Generic data structures for C-sets (presheaves).
"""
module CSets
export AbstractCSet, AbstractCSetType, CSet, CSetType, nparts, subpart,
  get_subpart, incident, add_part!, add_parts!, set_subpart!, set_subparts!

using Compat: only
using LabelledArrays, StaticArrays

using ...Present
using ...Theories: Category, dom, codom

# C-set data types
##################

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

Instead of filling out the type parameters yourself, you should use the function
[`CSetType`](@ref) to generate a `CSet` type from a presentation of a category.
Nevertheless, the first six type parameters are documented at
[`AbstractCSet`](@ref). The remaining type parameters are an implementation
detail and should be ignored.

Following LightGraphs.jl, the incidence vectors, stored in the `incidence`
field, are kept in sorted order. To ensure consistency, no field of the struct
should ever be mutated directly.
"""
mutable struct CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,NOb,NHom,NIndex} <:
       AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom}
  nparts::SLArray{Tuple{NOb},Int,1,NOb,Ob}
  subparts::SLArray{Tuple{NHom},Vector{Int},1,NHom,Hom}
  incident::SLArray{Tuple{NIndex},Vector{Vector{Int}},1,NIndex,Index}
  data::NamedTuple{Data}
end

function CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index}(; kw...) where
    {Ob,Hom,Dom,Codom,Data,DataDom,Index}
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index}((; kw...))
end
function CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index}(
    datatypes::NamedTuple{Data}) where {Ob,Hom,Dom,Codom,Data,DataDom,Index}
  # This function could be `@generated` for slight performance gain.
  NOb, NHom, NIndex = length(Ob), length(Hom), length(Index)
  @assert length(Dom) == NHom && length(Codom) == NHom
  @assert length(DataDom) == length(Data)
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,NOb,NHom,NIndex}(
    SLArray{Tuple{NOb},Ob}(zeros(SVector{NOb,Int})),
    SLArray{Tuple{NHom},Hom}(Tuple(Int[] for i in 1:NHom)),
    SLArray{Tuple{NIndex},Index}(Tuple(Vector{Int}[] for i in 1:NIndex)),
    NamedTuple{Data}(T[] for T in datatypes))
end

""" Generate an abstract C-set type from a presentation of a category.

See also: [`CSetType`](@ref).
"""
function AbstractCSetType(pres::Presentation{Category}; data=())
  Ob, Hom, Dom, Codom, Data, DataDom, _ = CSetTypeParams(pres, data=data)
  if isempty(Data)
    AbstractCSet{Ob,Hom,Dom,Codom}
  else
    AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom}
  end
end

""" Generate a C-set data type from a presentation of a category.

See also: [`AbstractCSetType`](@ref).
"""
function CSetType(pres::Presentation{Category}; data=(), index=())
  Ob, Hom, Dom, Codom, Data, DataDom, Index =
    CSetTypeParams(pres, data=data, index=index)
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index}
end
function CSetTypeParams(pres::Presentation{Category}; data=(), index=())
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  data_obs, obs = separate(ob -> nameof(ob) ∈ data, obs)
  data_homs, homs = separate(hom -> codom(hom) ∈ data_obs, homs)
  ob_index = ob -> findfirst(obs .== ob)::Int
  (Tuple(nameof.(obs)), Tuple(nameof.(homs)),
   Tuple(@. ob_index(dom(homs))), Tuple(@. ob_index(codom(homs))),
   Tuple(nameof.(data_homs)), Tuple(@. ob_index(dom(data_homs))), Tuple(index))
end
separate(f, a::AbstractArray) = (i = f.(a); (a[i], a[.!i]))

function Base.:(==)(x1::T, x2::T) where T <: CSet
  # The incidence data is redundant, so need not be compared.
  x1.nparts == x2.nparts && x1.subparts == x2.subparts && x1.data == x2.data
end

# C-set interface
#################

""" Number of parts of given type in a C-set.
"""
nparts(cset::CSet, type) = cset.nparts[type]

""" Get subpart of part in C-set.

Both single and vectorized access are supported.
"""
subpart(cset::CSet, part, name) = _subpart(cset, part, Val(name))

@generated function _subpart(
    cset::CSet{obs,homs,doms,codoms,data}, part,
    ::Val{name}) where {obs,homs,doms,codoms,data,name}
  if name ∈ homs
    :(cset.subparts.$name[part])
  elseif name ∈ data
    :(cset.data.$name[part])
  else
    throw(KeyError(name))
  end
end

""" Get subpart of part in C-set, with default if there is no such subpart.

The relationship between [`subpart`](@ref) and this function is the same as that
between `[` and `get` for dictionaries.
"""
function get_subpart(f, cset::CSet, part, name)
  value = get_subpart(cset, part, name, undef)
  value == undef ? f() : value
end

get_subpart(cset::CSet, part, name, default) =
  _get_subpart(cset, part, Val(name), default)

@generated function _get_subpart(
    cset::CSet{obs,homs,doms,codoms,data}, part,
    ::Val{name}, default) where {obs,homs,doms,codoms,data,name}
  if name ∈ homs
    :(cset.subparts.$name[part])
  elseif name ∈ data
    :(cset.data.$name[part])
  else
    :default
  end
end

""" Get superparts incident to part in C-set.
"""
incident(cset::CSet, part, name) = cset.incident[name][part]

""" Add part of given type to C-set, optionally setting its subparts.

Returns the ID of the added part.

See also: [`add_parts!`](@ref).
"""
add_part!(cset::CSet, type) = only(_add_parts!(cset, Val(type), 1))

function add_part!(cset::CSet, type, subparts)
  part = add_part!(cset, type)
  set_subparts!(cset, part, subparts)
  part
end

""" Add parts of given type to C-set, optionally setting their subparts.

Returns the range of IDs for the added parts.

See also: [`add_part!`](@ref).
"""
add_parts!(cset::CSet, type, n::Int) = _add_parts!(cset, Val(type), n)

function add_parts!(cset::CSet, type, n::Int, subparts)
  parts = add_parts!(cset, type, n)
  set_subparts!(cset, parts, subparts)
  parts
end

@generated function _add_parts!(
    cset::CSet{obs,homs,doms,codoms,data,data_doms,indexed},
    ::Val{type}, n::Int) where
    {obs,homs,doms,codoms,data,data_doms,indexed,type}
  ob = NamedTuple{obs}(eachindex(obs))[type]
  in_homs = [ homs[i] for (i, codom) in enumerate(codoms) if codom == ob ]
  out_homs = [ homs[i] for (i, dom) in enumerate(doms) if dom == ob ]
  data_homs = [ data[i] for (i, dom) in enumerate(data_doms) if dom == ob ]
  indexed_homs = filter(hom -> hom ∈ indexed, in_homs)
  # TODO: The three loops could (should?) be unrolled. Or is Julia's compiler
  # smart enough to do this on its own?
  quote
    @assert n > 0
    nparts = cset.nparts.$type + n
    cset.nparts = SLVector(cset.nparts; $type=nparts)
    start = nparts - n + 1
    for name in $(Tuple(out_homs))
      sub = cset.subparts[name]
      resize!(sub, nparts)
      @inbounds sub[start:nparts] .= 0
    end
    for name in $(Tuple(indexed_homs))
      incident = cset.incident[name]
      resize!(incident, nparts)
      @inbounds for part in start:nparts
        incident[part] = Int[]
      end
    end
    for name in $(Tuple(data_homs))
      resize!(cset.data[name], nparts)
    end
    start:nparts
  end
end

""" Mutate subpart of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subparts!`](@ref).
"""
function set_subpart!(cset::CSet, part::Int, name, subpart)
  _set_subpart!(cset, part, Val(name), subpart)
end
function set_subpart!(cset::CSet, part::AbstractVector{Int}, name, subpart)
  broadcast(part, subpart) do part, subpart
    _set_subpart!(cset, part, Val(name), subpart)
  end
end
@generated function _set_subpart!(
    cset::CSet{obs,homs,doms,codoms,data,data_doms,indexed},
    part::Int, ::Val{name}, subpart) where
    {obs,homs,doms,codoms,data,data_doms,indexed,name}
  if name ∈ indexed
    quote
      old = cset.subparts.$name[part]
      cset.subparts.$name[part] = subpart
      if old > 0
        deletesorted!(cset.incident.$name[old], part)
      end
      if subpart > 0
        insertsorted!(cset.incident.$name[subpart], part)
      end
    end
  elseif name ∈ homs
    :(cset.subparts.$name[part] = subpart)
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
function set_subparts!(cset::CSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(cset, part, name, subpart)
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

""" Computing with C-sets (presheaves).
"""
module CSets
export AbstractCSet, CSet, CSetType, nparts, subpart, incident,
  add_part!, add_parts!, set_subpart!, set_subparts!

using LabelledArrays, StaticArrays

using ...Present
using ...Theories: Category, FreeCategory, dom, codom

# C-sets
########

""" Abstract type for C-sets (presheaves).

TODO: Document type parameters

See also: [`CSet`](@ref).
"""
abstract type AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom} end

""" Data type for C-sets (presheaves).

The type parameters of this generic type should be considered an implementation
detail. Avoid instantiating them directly. Instead, use [`CSetType`](@ref) to
generate a `CSet` type from a presentation of a category `C`.

Following LightGraphs.jl, the incidence vectors are kept in sorted order. To
ensure consistency, no field of the struct should ever be mutated directly.
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
  NOb, NHom, NIndex = length(Ob), length(Hom), length(Index)
  @assert length(Dom) == NHom && length(Codom) == NHom
  @assert length(DataDom) == length(Data)
  CSet{Ob,Hom,Dom,Codom,Data,DataDom,Index,NOb,NHom,NIndex}(
    SLArray{Tuple{NOb},Ob}(zeros(SVector{NOb,Int})),
    SLArray{Tuple{NHom},Hom}([ Int[] for i in 1:NHom]),
    SLArray{Tuple{NIndex},Index}([ Vector{Int}[] for i in 1:NIndex ]),
    NamedTuple{Data}(T[] for T in datatypes))
end

""" Generate a C-set data type from a presentation of a category.
"""
function CSetType(pres::Presentation{Category}; data=(), index=())
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  data_obs, obs = separate(ob -> nameof(ob) ∈ data, obs)
  data_homs, homs = separate(hom -> codom(hom) ∈ data_obs, homs)
  ob_index = ob -> findfirst(obs .== ob)::Int
  CSet{Tuple(nameof.(obs)), Tuple(nameof.(homs)),
       Tuple(@. ob_index(dom(homs))), Tuple(@. ob_index(codom(homs))),
       Tuple(nameof.(data_homs)), Tuple(@. ob_index(dom(data_homs))),
       Tuple(index)}
end
separate(f, a::AbstractArray) = (i = f.(a); (a[i], a[.!i]))

function Base.:(==)(x1::T, x2::T) where T <: CSet
  # The incidence data is redundant, so need not be compared.
  x1.nparts == x2.nparts && x1.subparts == x2.subparts
end

nparts(cset::CSet, type) = cset.nparts[type]

subpart(cset::CSet, part::Union{Int,AbstractVector{Int}}, name) =
  _subpart(cset, part, Val(name))

@generated function _subpart(
    cset::CSet{obs,homs,doms,codoms,data}, part::Union{Int,AbstractVector{Int}},
    ::Val{name}) where {obs,homs,doms,codoms,data,name}
  # Allow both single and vectorized access.
  if name ∈ data
    :(cset.data.$name[part])
  else
    :(cset.subparts.$name[part])
  end
end

incident(cset::CSet, part::Int, name) = cset.incident[name][part]

""" Add part of given type to C-set, optionally setting its subparts.

See also: [`add_parts!`](@ref).
"""
add_part!(cset::CSet, type, args...) = add_parts!(cset, type, 1, args...)

""" Add parts of given type to C-set, optionally setting their subparts.

See also: [`add_part!`](@ref).
"""
add_parts!(cset::CSet, type, n::Int) = add_parts!(cset, type, n, NamedTuple())
add_parts!(cset::CSet, type, n::Int, subparts) =
  _add_parts!(cset, Val(type), n, subparts)

@generated function _add_parts!(
    cset::CSet{obs,homs,doms,codoms,data,data_doms,indexed},
    ::Val{type}, n::Int, subparts) where
    {obs,homs,doms,codoms,data,data_doms,indexed,type}
  ob = NamedTuple{obs}(eachindex(obs))[type]
  in_homs = [ homs[i] for (i, codom) in enumerate(codoms) if codom == ob ]
  out_homs = [ homs[i] for (i, dom) in enumerate(doms) if dom == ob ]
  data_homs = [ data[i] for (i, dom) in enumerate(data_doms) if dom == ob ]
  indexed_homs = filter(hom -> hom ∈ indexed, in_homs)
  # TODO: The first three loops could (should?) be unrolled. Or is Julia's
  # compiler smart enough to do this on its own?
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
    if !isempty(subparts)
      for part in start:nparts
        set_subparts!(cset, part, subparts)
      end
    end
    nparts
  end
end

""" Mutate subpart of a part in a C-set.

See also: [`set_subparts!`](@ref).
"""
function set_subpart!(cset::CSet, part, name, subpart)
  _set_subpart!(cset, part, Val(name), subpart)
end
@generated function _set_subpart!(
    cset::CSet{obs,homs,doms,codoms,data,data_doms,indexed},
    part, ::Val{name}, subpart) where
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
  elseif name ∈ data
    :(cset.data.$name[part] = subpart)
  else
    :(cset.subparts.$name[part] = subpart)
  end
end

""" Mutate subparts of a part in a C-set.

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

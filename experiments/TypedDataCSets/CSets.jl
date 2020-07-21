module CSets
export AbstractCSet, CSet, AbstractCSetType, CSetType, CSetTypeParams,
  TheoryDecGraph, RDecGraph

using LabelledArrays, StaticArrays, StructArrays

using Catlab.Present
using Catlab.Theories: Category, FreeCategory, dom, codom, compose

const NamedSVector{Names,T,N} = SLArray{Tuple{N},T,1,N,Names}

# Typed C-sets
##############


""" Typed C-sets (TCSets) are CSets with concrete types for their data morphisms
"""
abstract type AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom,DataTypes} end

mutable struct CSet{Ob,Hom,Dom,Codom,Data,DataDom,DataTypes,
                    HomTuple,DataTuple,Index,DataIndex,IsUnique} <:
                      AbstractCSet{Ob,Hom,Dom,Codom,Data,DataDom,DataTypes}
  obs::NamedTuple{Ob,HomTuple}
  indices::NamedSVector{Index,Vector{Vector{Int}}}
  data::NamedTuple{Ob,DataTuple}
  data_indices::NamedTuple{DataIndex}
end

function AbstractCSetType(pres::Presentation{Category}; data=(), datatypes=())
  # Only include `Data` and `DataDom` params if there are data morphisms.
  Ts = CSetTypeParams(pres, data=data, datatypes=datatypes)
  AbstractCSet{(isempty(Ts[5]) ? Ts[1:4] : Ts[1:7])...}
end

""" Generate a C-set data type from a presentation of a category.

See also: [`AbstractCSetType`](@ref).
"""
function CSetType(pres::Presentation{Category}; kw...)
  CSet{CSetTypeParams(pres; kw...)...}
end

separate(f, a::AbstractArray) = (i = f.(a); (a[i], a[.!i]))

function CSetTypeParams(pres::Presentation{Category};
                        data=(), datatypes=Dict{Symbol,DataType}(), index=(), unique_index=())
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  data_obs, obs = separate(ob -> nameof(ob) ∈ data, obs)
  data_homs, homs = separate(hom -> codom(hom) ∈ data_obs, homs)
  data_index, index = separate(name -> name ∈ nameof.(data_homs),
                               sort!(index ∪ unique_index))
  homs_by_ob = Dict{Symbol,Array}(nameof(ob) => [] for ob in obs)
  for h in homs
    push!(homs_by_ob[nameof(dom(h))],h)
  end
  data_by_ob = Dict{Symbol,Array}(nameof(ob) => [] for ob in obs)
  for h in data_homs
    push!(data_by_ob[nameof(dom(h))],h)
  end
  hom_svector(homs) = NamedSVector{Tuple(nameof.(homs)),Vector{Int}}
  hom_tuple = NamedTuple{Tuple(nameof.(obs)), Tuple{[hom_svector(homs_by_ob[nameof(ob)]) for ob in obs]...}}

  data_struct_array(homs) = StructArray{Tuple(nameof.(homs)),Tuple{[datatypes[nameof(h)] for h in homs]...}}
  data_tuple = NamedTuple{Tuple(nameof.(obs)), Tuple{[data_struct_array(data_by_ob[nameof(ob)]) for ob in obs]...}}

  ob_num = ob -> findfirst(obs .== ob)::Int
  (Tuple(nameof.(obs)), Tuple(nameof.(homs)),
   Tuple(@. ob_num(dom(homs))), Tuple(@. ob_num(codom(homs))),
   Tuple(nameof.(data_homs)), Tuple(@. ob_num(dom(data_homs))),
   hom_tuple, data_tuple,
   Tuple(index), Tuple(data_index), Tuple(k ∈ unique_index for k in data_index))
end

# Example: Real-Decorated Graphs
################################

@present TheoryDecGraph(FreeCategory) begin
  V::Ob
  E::Ob
  num::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
  dec::Hom(V,num)
end

const RDecGraph = CSetType(TheoryDecGraph, data=(:num,), datatypes=Dict(:dec=>Float64))

end

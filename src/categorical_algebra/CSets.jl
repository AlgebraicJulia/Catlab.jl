""" Computing with C-sets (presheaves).
"""
module CSets
export CSet, nparts, subpart, incident, add_part!

using AutoHashEquals
using LabelledArrays

@auto_hash_equals struct CSet{
    NParts <: (SLArray{Tuple{N},Int,1} where N),
    SubParts <: (SLArray{Tuple{N},Vector{Int},1} where N),
    Incident <: (SLArray{Tuple{N},Vector{Vector{Int}},1} where N)
  }
  nparts::NParts
  subparts::SubParts
  incident::Incident
end

nparts(cset::CSet, type) = cset.nparts[type]

function subpart(cset::CSet, name, part::Union{Int,AbstractVector{Int}})
  # Allow both single and vectorized access.
  cset.subparts[name][part]
end

incident(cset::CSet, name, part::Int) = cset.incident[name][part]

function add_part!(cset::CSet, type, subparts)
  part = cset.nparts[type] += 1
  for (name, subpart) in pairs(subparts)
    push!(cset.subparts[name], subpart)
    push!(cset.incident[name][subpart], part)
  end
  part
end

end

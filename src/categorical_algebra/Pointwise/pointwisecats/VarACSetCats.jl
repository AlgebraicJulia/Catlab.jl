using ACSets
using ACSets.DenseACSets: attrtype_type
using ..ACSetTransformations

export abstract_attributes

"""
For any ACSet, X, a canonical map A→X where A has distinct variables for all
attributes valued in attrtypes present in `abstract` (by default: all attrtypes)
"""
function abstract_attributes(X::ACSet, abstract=nothing)
  S = acset_schema(X)
  abstract = isnothing(abstract) ? attrtypes(S) : abstract
  A = copy(X)
  comps = Dict{Any, Any}(map(abstract) do at
    rem_parts!(A, at, parts(A, at))
    comp = Union{AttrVar, attrtype_type(X, at)}[]
    for (f, d, _) in attrs(S; to=at)
      append!(comp, X[f])
      A[f] = AttrVar.(add_parts!(A, at, nparts(A, d)))
    end
    at => comp
  end)
  for o in ob(S) comps[o]=parts(X,o) end
  return ACSetTransformation(A,X; comps...)
end 

abstract_attributes(f::ACSetTransformation) = abstract_attributes(dom(f)) ⋅ f

"""
Find some part + attr that refers to an AttrVar. 
Throw error if none exists (i.e. `i` is a wandering variable).
"""
function var_reference(X::ACSet, at::Symbol, i::Int)
  S = acset_schema(X)
  for (f, c, _) in attrs(S; to=at)
    inc = incident(X, AttrVar(i), f)
    if !isempty(inc)
      return (f, c, first(inc))
    end
  end
  error("Wandering variable $at#$p")
end

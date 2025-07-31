
using ....BasicSets: SetFunction
using ..CSets, ..PointwiseCats
import ..CSets: ACSetTransformation, _ACSetTransformation
import ..ACSetTransformations: infer_acset_cat


# TODO use the actual component data for finer granularity
""" 
Sensible defaults for interpreting an ACSetTransformation as living in a
particular kind of ACSet category 
"""
function infer_acset_cat(comps, X::ACSet{PT}, Y::ACSet)::ACSetCategory where PT
  S = acset_schema(X)
  cat = if isempty(attrtypes(S))
    PT == IntParts ? CSetCat : MADCSetCat
  elseif hasvar(X) || hasvar(Y) 
    PT == IntParts ? VarACSetCat : MADVarACSetCat
  else 
    if PT == IntParts 
      loose = any(o -> haskey(comps, o) && comps[o] isa SetFunction, attrtypes(S))
      loose ? LooseACSetCat : ACSetCat
    else
      MADACSetCat
    end
  end
  return ACSetCategory(cat(X))
end

function infer_acset_cat(X::ACSet{PT})::ACSetCategory where PT
  S = acset_schema(X)
  cat = if isempty(attrtypes(S))
    PT == IntParts ? CSetCat : MADCSetCat
  elseif hasvar(X)
    PT == IntParts ? VarACSetCat : MADVarACSetCat
  else 
    PT == IntParts ? ACSetCat : MADACSetCat
  end
  return ACSetCategory(cat(X))
end

function hasvar(X::ACSet, x)
  s = acset_schema(X)
  (x∈ attrs(acset_schema(X),just_names=true) && hasvar(X,codom(s,x))) || 
  x∈attrtypes(acset_schema(X)) && nparts(X,x)>0
end

hasvar(X::ACSet) = any(o->hasvar(X,o), attrtypes(acset_schema(X)))
  
function ACSetTransformation(comps, dom::ACSet, codom::ACSet; 
                             cat::Union{Nothing,ACSetCategory}=nothing)
  cat = isnothing(cat) ? infer_acset_cat(comps, dom, codom) : cat
  return coerce(_ACSetTransformation(comps, dom, codom); cat)
end

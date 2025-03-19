export FinDomFunction, ThFinDomFunction, coerce_findom, ensure_indexed, precompose

using StructEquality
import ACSets.Columns: preimage, Column
using GATlab

import ....Theories: dom, codom
using ..Sets: ProdSet, SetOb
using ..FinSets: FinSet, FinSetInt, FinSetAsSet, ProdFinSet, FinSetHash
using ..SetFunctions
using ..SetFunctions: ThFunctionCore
import ..FinFunctions: is_indexed, is_monic
import .ThSetFunction: dom, codom, app, postcompose
using ..FinFunctions

# FinDomFunctions
##################

""" This is only subtyped by FinFunction """
abstract type FinDomFunction′ end 


"""
A FinDomFunction is a kind of heteromorphism between the categories Set and 
FinSet. This means we can pick out a domain FinSet and codomain set, we apply 
the function to any domain element to get a codomain element, and we can 
precompose with FinFunctions and postcompose with SetFunctions to get another 
FinDomFunction.
"""
@theory ThFinDomFunction <: ThFunctionCore begin
  Fun′::TYPE{FinDomFunction′}
  SFun::TYPE{SetFunction}
  DomSet::TYPE{FinSet}
  CodSet::TYPE{SetOb}
  dom()::DomSet # eltype(dom()) <: Dom
  codom()::CodSet # eltype(codom()) <: Cod
  postcompose(t::SFun)::Fun′
end

ThFinDomFunction.Meta.@wrapper FinDomFunction <: FinDomFunction′

Base.show(io::IO, f::FinDomFunction) = show(io, getvalue(f))

(f::FinDomFunction)(i) = app(f, i)

# Common code to FinFunctions and FinDomFunctions
#################################################

"""
Whether something is monic is a holistic property of a morphism in the context 
of a whole category. This function implicitly interprets FinDomFunctions as 
heteromorphisms in the collage of the embedding of FinSet into Set.
"""
is_monic(f::FinDomFunction) = length(dom(f)) == length(Set(values(collect(f))))

""" Iterate over image of function """
Base.iterate(f::Union{FinFunction, FinDomFunction}, xs...) = iterate(f.(dom(f)), xs...)

Base.length(f::Union{FinFunction, FinDomFunction}) = length(dom(f))

Base.eltype(f::Union{FinFunction, FinDomFunction}) = eltype(codom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::Union{FinFunction, FinDomFunction}, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(f), x) # use cached value
  filter(y -> f(y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

""" A FinDomFunction is indexed iff its implementation is """
is_indexed(f::FinDomFunction) = is_indexed(getvalue(f))


""" If an implementation specifically comes with its own `preimage` method, we 
consider the SetFunction to be indexed """
# is_indexed(::T) where T = !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::T) where {T<:Union{FinFunction, FinDomFunction}}
  is_indexed(f) && return f
  if getvalue(dom(f)) isa FinSetInt
    return T(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

ensure_indexed(f::SetFunction) = f

""" Common method for `precompose` agnostic to which implementation one uses """
function precompose(model::FinDomFunction, f::FinFunction)::FinDomFunction
  new_vals = if getvalue(dom(f)) isa FinSetInt
     [app(model, f(i)) for i in dom(f)]
  else 
    Dict(k => f(i) for i in dom(f))
  end
  FinDomFunction(new_vals, codom(model); index=is_indexed(model))
end

function coerce_findom(s::SetFunction)
  d = getvalue(dom(s))
  if d isa FinSetAsSet
    d = getvalue(getvalue(d))
    if d isa FinSetInt 
      return FinDomFunction([s(i) for i in d], codom(s))
    elseif d isa FinSetHash 
      return FinDomFunction(Dict(k=>s(k) for k in getvalue(d)), FinSet(d), codom(s))  
    end
  elseif d isa ProdSet && all(x->getvalue(x) isa FinSetAsSet, d)
    new_dom = FinSet(ProdFinSet(d))
    return FinDomFunction(Dict(k=>s(k) for k in new_dom), new_dom, codom(s))
  end

  error("Cannot coerce $s to a `FinDomFunction`: \ndomain $d :: $(typeof(d))")
end

# ACSet Interface
#################

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

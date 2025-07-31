module FinDomFunctions 

export FinDomFunction, FinDomFunction′, ThFinDomFunction, is_indexed, AbstractFunction, ensure_indexed, precompose, is_monic, is_iso

using StructEquality
import ACSets.Columns: preimage, Column
using GATlab

import ....Theories: dom, codom
using ..BasicSets: SetOb, ThFunctionCore, ThSetFunction, SetFunction, FinFunction, is_epic, UnitRangeLike
import ..FinSets: ≃
import .ThSetFunction: dom, codom, app, postcompose

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

const AbstractFunction = Union{SetFunction, FinFunction, FinDomFunction}

Base.show(io::IO, f::FinDomFunction) = show(io, getvalue(f))

(f::FinDomFunction)(i) = app(f, i)

# Common code to FinFunctions and FinDomFunctions
#################################################

""" Extensional equality of FinFunctions """
function ≃(f::FinFunction, g::FinFunction)
  f == g && return true
  all([dom(f) ≃ dom(g), codom(f) ≃ codom(g), all(i->f(i)==g(i), dom(f))])
end

""" Extensional equality of FinDomFunctions """
function ≃(f::FinDomFunction, g::FinDomFunction) 
  f == g && return true
  all([dom(f) ≃ dom(g), codom(f) == codom(g), all(i->f(i)==g(i), dom(f))])
end
"""
Whether something is monic is a holistic property of a morphism in the context 
of a whole category. This function implicitly interprets FinDomFunctions as 
heteromorphisms in the collage of the embedding of FinSet into Set.
"""
is_monic(f::Union{FinFunction, FinDomFunction}) =   
  length(dom(f)) == length(Set(values(collect(f))))

is_iso(f::Union{FinFunction, FinDomFunction}) = is_monic(f) && is_epic(f)

function Base.collect(f::Union{FinDomFunction,FinFunction}) 
  res = eltype(codom(f))[]
  for i in collect(dom(f))
    push!(res, app(f, i))
  end
  res
end

Base.Dict(f::Union{FinFunction, FinDomFunction}) = Dict(map(dom(f)) do i 
  i => f(i)
end)


Base.length(f::Union{FinFunction, FinDomFunction}) = length(dom(f))

Base.eltype(f::Union{FinFunction, FinDomFunction}) = eltype(codom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::Union{FinFunction, FinDomFunction}, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(f), x) # use cached value
  filter(y -> app(f,y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

""" A FinDomFunction is indexed iff its implementation is """
is_indexed(f::Union{FinFunction,FinDomFunction}) = is_indexed(getvalue(f))
is_indexed(f) = false # false by default

""" If an implementation specifically comes with its own `preimage` method, we 
consider the SetFunction to be indexed """
# is_indexed(::T) where T = !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::T) where {T<:AbstractFunction}
  is_indexed(f) && return f
  if getvalue(dom(f)) isa UnitRangeLike
    return T(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

""" Common method for `precompose` agnostic to which implementation one uses """
function precompose(model::FinDomFunction, f::FinFunction)::FinDomFunction
  D, C = impl_type(f, :Dom), impl_type(model, :Cod)
  new_vals = if getvalue(dom(f)) isa UnitRangeLike
     C[app(model, f(i)) for i in dom(f)]
  else 
    Dict{D,C}(i => app(model, f(i)) for i in dom(f))
  end
  FinDomFunction(new_vals, codom(model); index=is_indexed(model))
end

FinDomFunction(f::FinFunction, g::FinDomFunction) = precompose(g, f)

FinDomFunction(f::FinDomFunction, g::FinFunction) = postcompose(f, g)

# ACSet Interface
#################

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

end # module

module FinFunctions 
export FinFunction, FinDomFunction, preimage, is_indexed,
       is_monic, is_epic, is_iso

using Reexport

import ACSets.Columns: preimage, Column
using GATlab: getvalue

using ..FinSets: FinSet, FinSetInt
using ..SetFunctions: SetFunction, SetFunctionImpl, dom, codom
import ..SetFunctions: force

# Finite functions
##################

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explicitly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

FinFunctions can be constructed with or without an explicitly provided codomain.
If a codomain is provided, by default the constructor checks it is valid.

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
const FinFunction = SetFunction{FinSet,FinSet}

const FinDomFunction = SetFunction{FinSet}

""" 
Special `force` method for FinDomFunction - we know we can normalize to a 
FinFunctionDict or FinFunctionVect
"""
function force(s::FinDomFunction)::SetFunction
  i = getvalue(s)
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return FinDomFunction(collect(s), codom(s))
  else
    i isa FinFunctionDict && return s 
    return FinDomFunction(Dict(k => s(k) for k in dom(s)), codom(s))
  end
end

# These could be made to fail early if ever used in performance-critical areas
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))

is_monic(f::FinDomFunction) = length(dom(f)) == length(Set(values(collect(f))))

is_iso(f::FinDomFunction) = is_monic(f) && is_epic(f)

""" Iterate over image of function """
Base.iterate(f::FinDomFunction, xs...) = iterate(f.(dom(f)), xs...)

Base.length(f::FinDomFunction) = length(dom(f))

Base.eltype(f::FinDomFunction) = eltype(codom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::FinDomFunction, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(f), x) # use cached value
  filter(y -> f(y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

""" A SetFunction is indexed iff its implementation is """
is_indexed(f::SetFunction) = is_indexed(getvalue(f))

""" If an implementation specifically comes with its own `preimage` method, we 
consider the SetFunction to be indexed """
is_indexed(::T) where {T<:SetFunctionImpl} = !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::FinDomFunction)
  is_indexed(f) && return f
  if getvalue(f) isa FinFunctionVector
    return FinDomFunction(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

# ACSet Interface
#################
FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(
    Int[c[i] for i in dom], codom
  )

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)


# Implementations
#################

include("FinFnImpls/FinFnVector.jl")
include("FinFnImpls/FinFnDict.jl")

@reexport using .FinFnVector 
@reexport using .FinFnDict

end # module

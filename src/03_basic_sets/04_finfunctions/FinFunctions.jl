export FinFunction, FinDomFunction, preimage, is_indexed,
       is_monic, is_epic, is_iso, Fin_FinDom, ensure_indexed


import ACSets.Columns: preimage, Column
using GATlab: getvalue

using ..FinSets: AbsSet, FinSet, FinSetInt
# import ..SetFunctions: force
using ..SetFunctions: SetFunction, dom, codom

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
const FinFunction = SetFunction{Any, SetFunction, FinSet, FinSet}

const FinDomFunction = SetFunction{Any, SetFunction, FinSet, AbsSet}

const Fin_FinDom = Union{FinFunction, FinDomFunction}

# These could be made to fail early if ever used in performance-critical areas
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))

is_monic(f::Fin_FinDom) = length(dom(f)) == length(Set(values(collect(f))))

is_iso(f::Fin_FinDom) = is_monic(f) && is_epic(f)

""" Iterate over image of function """
Base.iterate(f::Fin_FinDom, xs...) = iterate(f.(dom(f)), xs...)

Base.length(f::Fin_FinDom) = length(dom(f))

Base.eltype(f::Fin_FinDom) = eltype(codom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::Fin_FinDom, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(f), x) # use cached value
  filter(y -> f(y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

""" A SetFunction is indexed iff its implementation is """
is_indexed(f::SetFunction) = is_indexed(getvalue(f))

""" If an implementation specifically comes with its own `preimage` method, we 
consider the SetFunction to be indexed """
is_indexed(::T) where T = !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::T) where {T<:Fin_FinDom}
  is_indexed(f) && return f
  if getvalue(f) isa FinFunctionVector
    return T(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

# Force
#######

"""
`force` behaves differently when the domain is finite because we can compute 
a normal form. This should really be called "normalize". It coerces the 
function to a `FinFnVector` (if dom is `FinSetInt`) or `FinFnDict` (otherwise).
"""
# function force(s::Union{FinFunction, FinDomFunction})::FinDomFunction
#   if getvalue(dom(s)) isa FinSetInt 
#     FinDomFunction(collect(s), codom(s))
#   else 
#     FinDomFunction(Dict(k=>s(k) for k in dom(s)), dom(s), codom(s))
#   end
# end



# ACSet Interface
#################
FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(
    Int[c[i] for i in dom], codom
  )

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

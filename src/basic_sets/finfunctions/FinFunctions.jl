
export FinFunction, FinDomFunction, force, is_indexed, preimage, is_monic, is_epic, is_iso

using StaticArrays: StaticVector, SVector
import ACSets.Columns: preimage

using ....Theories: dom, codom
using ..Sets, ..FinSets, ..SetFunctions

# Finite functions
##################

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

FinFunctions can be constructed with or without an explicitly provided codomain.
If a codomain is provided, by default the constructor checks it is valid.

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
const FinFunction{S, S′, Dom <: FinSet{S}, Codom <: FinSet{S′}} =
  SetFunction{Dom,Codom}

FinFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), FinSet(codom))
FinFunction(::typeof(identity), args...) =
  IdentityFunction((FinSet(arg) for arg in args)...)
FinFunction(f::AbstractDict, args...) =
  FinFunctionDict(f, (FinSet(arg) for arg in args)...)

function FinFunction(f::AbstractVector, args...;
                     index=false, known_correct = false, 
                     dom_parts=nothing, codom_parts=nothing)
  cod = FinSet(isnothing(codom_parts) ? args[end] : codom_parts)
  f = Vector{Int}(f) # coerce empty vectors
  if !known_correct
    for (i,t) ∈ enumerate(f)
      if isnothing(dom_parts) || i ∈ dom_parts
        t ∈ cod || error("Value $t at index $i is not in $cod.")
      end
    end
  end
  if !index
    if !isnothing(dom_parts) 
      args = (length(f), args[2:end]...)
    end
    FinDomFunctionVector(f, (FinSet(arg) for arg in args)...)
  else
    index = index == true ? nothing : index
    IndexedFinFunctionVector(f, cod; index=index)
  end
end
#Below method stops previous method from being called without a codomain
FinFunction(f::AbstractVector{Int}; kw...) =
  FinFunction(f, FinSet(isempty(f) ? 0 : maximum(f)); kw...)

SetFunctions.show_type_constructor(io::IO, ::Type{<:FinFunction}) =
  print(io, "FinFunction")

""" Function out of a finite set.

This class of functions is convenient because it is exactly the class that can
be represented explicitly by a vector of values from the codomain.
"""
const FinDomFunction{S, Dom<:FinSet{S}, Codom<:SetOb} = SetFunction{Dom,Codom}

FinDomFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), codom)
FinDomFunction(::typeof(identity), args...) =
  IdentityFunction((FinSet(arg) for arg in args)...)
FinDomFunction(f::AbstractDict, args...) = FinDomFunctionDict(f, args...)
FinDomFunction(f::FinDomFunction) = f

#kw is to capture is_correct, which does nothing for this type.
function FinDomFunction(f::AbstractVector, args...; index=false, kw...)
  if index == false
    FinDomFunctionVector(f, args...)
  else
    index = index == true ? nothing : index
    IndexedFinDomFunctionVector(f, args...; index=index)
  end
end
#Below method stops above method from being called without a codomain
FinDomFunction(f::AbstractVector{T}; kw...) where T =
  FinDomFunction(f,TypeSet(T); kw...)

SetFunctions.show_type_constructor(io::IO, ::Type{<:FinDomFunction}) =
  print(io, "FinDomFunction")

""" The preimage (inverse image) of the value y in the codomain.
"""
preimage(f::IdentityFunction, y) = SVector(y)
preimage(f::FinDomFunction, y) = [ x for x in dom(f) if f(x) == y ]


# These could be made to fail early if ever used in performance-critical areas
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))
is_monic(f::FinFunction) = length(dom(f)) == length(Set(values(collect(f))))
is_iso(f::FinFunction) = is_monic(f) && is_epic(f)



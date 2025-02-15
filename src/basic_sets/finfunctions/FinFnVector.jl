module FinFnVector 
export FinDomFunctionVector, FinFunctionVector, IndexedFinFunctionVector, 
       IndexedFinDomFunctionVector, is_indexed

using StructEquality
using StaticArrays: StaticVector, SVector

import ....Theories: dom, codom
using ..Sets, ..FinSets, ..SetFunctions, ..FinFunctions 
import ..FinFunctions: preimage

# Vector-based functions
#-----------------------

""" Function in **Set** represented by a vector.

The domain of this function is always of type `FinSet{Int}`, with elements of
the form ``{1,...,n}``.
"""
@struct_hash_equal struct FinDomFunctionVector{T,V<:AbstractVector{T}, Codom<:SetOb{T}} <:
    SetFunction{FinSetInt,Codom}
  func::V
  codom::Codom
end

FinDomFunctionVector(f::AbstractVector{T}) where T =
  FinDomFunctionVector(f, TypeSet{T}())

function FinDomFunctionVector(f::AbstractVector, dom::FinSet{Int}, codom)
  length(f) == length(dom) ||
    error("Length of vector $f does not match domain $dom")
  FinDomFunctionVector(f, codom)
end

dom(f::FinDomFunctionVector) = FinSet(length(f.func))

(f::FinDomFunctionVector)(x) = f.func[x]

function Base.show(io::IO, f::FinDomFunctionVector)
  print(io, "FinDomFunction($(f.func), ")
  SetFunctions.show_domains(io, f)
  print(io, ")")
end

Base.collect(f::SetFunction) = force(f).func

""" Function in **FinSet** represented explicitly by a vector.
"""
const FinFunctionVector{S,T,V<:AbstractVector{T}} =
  FinDomFunctionVector{T,V,<:FinSet{S,T}}

Base.show(io::IO, f::FinFunctionVector) =
  print(io, "FinFunction($(f.func), $(length(dom(f))), $(length(codom(f))))")



# Indexed vector-based functions
#-------------------------------

""" Indexed function out of a finite set of type `FinSet{Int}`.

Works in the same way as the special case of [`IndexedFinFunctionVector`](@ref),
except that the index is typically a dictionary, not a vector.
"""
struct IndexedFinDomFunctionVector{T,V<:AbstractVector{T},Index,Codom<:SetOb{T}} <:
    SetFunction{FinSetInt,Codom}
  func::V
  index::Index
  codom::Codom
end

IndexedFinDomFunctionVector(f::AbstractVector{T}; kw...) where T =
  IndexedFinDomFunctionVector(f, TypeSet{T}(); kw...)

function IndexedFinDomFunctionVector(f::AbstractVector{T}, codom::SetOb{T};
                                     index=nothing) where T
  if isnothing(index)
    index = Dict{T,Vector{Int}}()
    for (i, x) in enumerate(f)
      push!(get!(index, x) do; Int[] end, i)
    end
  end
  IndexedFinDomFunctionVector(f, index, codom)
end
function IndexedFinDomFunctionVector(f::AbstractVector{T}, dom::FinSet{Int},
                                     codom::SetOb{T}; index=nothing) where T
  length(f) == length(dom) ||
    error("Length of vector $f does not match domain $dom")
  IndexedFinDomFunctionVector(f, index, codom)
end
Base.hash(f::IndexedFinDomFunctionVector, h::UInt) =
  hash(f.func, hash(f.codom, h))
Base.:(==)(f::Union{FinDomFunctionVector,IndexedFinDomFunctionVector},
           g::Union{FinDomFunctionVector,IndexedFinDomFunctionVector}) =
  # Ignore index when comparing for equality.
  f.func == g.func && codom(f) == codom(g)

function Base.show(io::IO, f::IndexedFinDomFunctionVector)
  print(io, "FinDomFunction($(f.func), ")
  SetFunctions.show_domains(io, f)
  print(io, ", index=true)")
end

dom(f::IndexedFinDomFunctionVector) = FinSet(length(f.func))

(f::IndexedFinDomFunctionVector)(x) = f.func[x]

""" Whether the given function is indexed, i.e., supports efficient preimages.
"""
is_indexed(f::SetFunction) = false
is_indexed(f::IdentityFunction) = true
is_indexed(f::IndexedFinDomFunctionVector) = true
is_indexed(f::FinDomFunctionVector{T,<:AbstractRange{T}}) where T = true


""" Indexed function between finite sets of type `FinSet{Int}`.

Indexed functions store both the forward map ``f: X → Y``, as a vector of
integers, and the backward map ``f: Y → X⁻¹``, as a vector of vectors of
integers, accessible through the [`preimage`](@ref) function. The backward map
is called the *index*. If it is not supplied through the keyword argument
`index`, it is computed when the object is constructed.

This type is mildly generalized by [`IndexedFinDomFunctionVector`](@ref).
"""
const IndexedFinFunctionVector{V,Index} =
  IndexedFinDomFunctionVector{Int,V,Index,FinSetInt}

function IndexedFinFunctionVector(f::AbstractVector{Int}; index=nothing)
  codom = isnothing(index) ? (isempty(f) ? 0 : maximum(f)) : length(index)
  IndexedFinFunctionVector(f, codom; index=index)
end

function IndexedFinFunctionVector(f::AbstractVector{Int}, codom; index=nothing)
  codom = FinSet(codom)
  if isnothing(index)
    index = [ Int[] for j in codom ]
    for (i, j) in enumerate(f)
      push!(index[j], i)
    end
  elseif length(index) != length(codom)
    error("Index length $(length(index)) does not match codomain $codom")
  end
  IndexedFinDomFunctionVector(f, codom, index=index)
end

function IndexedFinFunctionVector(f::AbstractVector{Int},dom,codom; index=nothing)
  IndexedFinFunctionVector(f,codom;index=index)
end

Base.show(io::IO, f::IndexedFinFunctionVector) =
  print(io, "FinFunction($(f.func), $(length(dom(f))), $(length(codom(f))), index=true)")


preimage(f::FinDomFunctionVector{T,<:AbstractRange{T}}, y::T) where T =
  # Both `in` and `searchsortedfirst` are specialized for AbstractRange.
  y ∈ f.func ? SVector(searchsortedfirst(f.func, y)) : SVector{0,Int}()

preimage(f::IndexedFinDomFunctionVector, y) = get_preimage_index(f.index, y)
@inline get_preimage_index(index::AbstractDict, y) = get(index, y, 1:0)
@inline get_preimage_index(index::AbstractVector, y) = index[y]

end # module
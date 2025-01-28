module FinFnVector 

export AbsFinFunctionVector, FinFunctionVector, IndexedFinFunctionVector

using StructEquality
using DataStructures

using GATlab
import ACSets.Columns: preimage

using ...Sets: AbsSet
using ...SetFunctions: ThSetFunction, SetFunction, codom
using ...FinSets: FinSet
import ..FinFunctions: FinFunction, FinDomFunction, is_indexed

"""
There are two kinds of FinFunctionVector: `FinFunctionVector` and 
`IndexedFinFunctionVector`.
"""
abstract type AbsFinFunctionVector{T} end

""" Implicitly domain is `FinSet(length(v))` """
@struct_hash_equal struct FinFunctionVector{T<:AbsSet} <: AbsFinFunctionVector{T}
  val::AbstractVector
  codom::T
end

"""  Implicitly domain is `FinSet(length(v))` """
@struct_hash_equal struct IndexedFinFunctionVector{T<:AbsSet} <: AbsFinFunctionVector{T}
  val::AbstractVector
  codom::T
  index::DefaultDict
  """ Create the index cache upon creating the vector """
  function IndexedFinFunctionVector(v, c::T) where T
    index = DefaultDict{eltype(c), Vector{Int}}(()->[])
    for (i, x) in enumerate(v)
      push!(index[x], i)
    end
    new{T}(v, c, index)
  end
end

FF(i::Bool) = i ? IndexedFinFunctionVector : FinFunctionVector

# Accessor
##########

GATlab.getvalue(f::AbsFinFunctionVector) = f.val

# Other methods
###############

preimage(f::IndexedFinFunctionVector, x) = f.index[x]

function Base.show(io::IO, f::AbsFinFunctionVector)
  print(io, "Fin")
  f.codom isa FinSet || print(io, "Dom")  
  print(io, "Function($(getvalue(f)), ")
  print(io, f.codom)
  is_indexed(f) &&  print(io, ", index=true")
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThSetFunction{Any, SetFunction, FinSet, T} [model::AbsFinFunctionVector{T}] where {
    T} begin

  dom()::AbsSet = FinSet(length(getvalue(model)))

  codom()::T = model.codom

  app(i::Any)::Any = getvalue(model)[i]

  function postcompose(f::SetFunction)::SetFunction
    FinDomFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end

end

# Default constructors
######################

""" 
Default `FinFunction` or `FinDomFunction` from a `AbstractVector` and codom
"""
FinFunction(f::AbstractVector, cod::FinSet; index=false) = 
  FinFunction(FF(index)(f, cod))

function FinDomFunction(f::AbstractVector, cod::AbsSet; index=false)  
  FinDomFunction(FF(index)(f, cod))
end

FinFunction(f::AbstractVector, dom::FinSet, cod::FinSet; index=false) = 
  dom == FinSet(length(f)) ? FinFunction(f, cod; index) : error(
    "Bad domain $dom for vector $f")

FinDomFunction(f::AbstractVector, dom::FinSet, cod::AbsSet; index=false) = 
    dom == FinSet(length(f)) ? FinDomFunction(f, cod; index) : error(
      "Bad domain $dom for vector $f")
  

const Maybe{T} = Union{T, Nothing}

""" Default `FinFunction` between `FinSetInt`s. """
FinFunction(f::AbstractVector{Int}, cod::Maybe{Int}=nothing; index=false) = 
  FinFunction(f, FinSet(isnothing(cod) ? maximum(f) : cod); index)
  
FinDomFunction(f::AbstractVector, cod::Maybe{Int}=nothing; index=false) = 
  FinFunction(f, cod; index)

""" Explicitly pass domain and check it's correct """
FinFunction(f::AbstractVector, dom::Int, cod::Int; index=false) = 
  length(f) == dom ? FinFunction(f, FinSet(cod); index) : error(
    "Mismatched dom=$dom for vector $f ($(length(f)))")

end # module

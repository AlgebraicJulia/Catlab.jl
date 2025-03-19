module FinFnVector 

export AbsFinFunctionVector, FinFunctionVector, IndexedFinFunctionVector

using StructEquality
using DataStructures

using GATlab
import ACSets.Columns: preimage

using ...FinSets: FinSet
using ..FinFunctions: dom, codom, ThFinFunction, FinFunction′
import ..FinFunctions: FinFunction, is_indexed

"""
There are two kinds of FinFunctionVector: `FinFunctionVector` and 
`IndexedFinFunctionVector`.
"""
abstract type AbsFinFunctionVector{C} end

""" Implicitly domain is `FinSet(length(v))`. Codomain is FinSet. """
@struct_hash_equal struct FinFunctionVector{C} <: AbsFinFunctionVector{C}
  val::AbstractVector
  codom::FinSet
  function FinFunctionVector(val::AbstractVector,codom::FinSet; check=false)
    if check 
      for (i,v) in enumerate(val)
        v ∈ codom || error("Bad FinFunctionVector value #$i: $v not in $codom")
      end
    end 
    new{eltype(codom)}(val, codom)
  end
end

"""  Implicitly domain is `FinSet(length(v))` """
@struct_hash_equal struct IndexedFinFunctionVector{C} <: AbsFinFunctionVector{C}
  val::AbstractVector
  codom::FinSet
  index::DefaultDict
  """ Create the index cache upon creating the vector """
  function IndexedFinFunctionVector(v, c::FinSet; check=false)
    index = DefaultDict{eltype(c), Vector{Int}}(()->[])
    for (i, x) in enumerate(v)
      check && x ∉ c && error("Bad FinFunctionVector value #$i: $x not in $c")
      push!(index[x], i)
    end
    new{eltype(codom)}(v, c, index)
  end
end

is_indexed(::IndexedFinFunctionVector) = true

FF(i::Bool) = i ? IndexedFinFunctionVector : FinFunctionVector

GATlab.getvalue(f::AbsFinFunctionVector) = f.val

preimage(f::IndexedFinFunctionVector, x) = f.index[x]

function Base.show(io::IO, f::AbsFinFunctionVector)
  print(io, "FinFunction($(getvalue(f)), ")
  print(io, f.codom)
  is_indexed(f) &&  print(io, ", index=true")
  print(io, ")")
end

# ThFinDomFunction implementation
############################

@instance ThFinFunction{Int,C} [model::AbsFinFunctionVector{C}] where {C} begin

  dom()::FinSet = FinSet(length(getvalue(model)))

  codom()::FinSet = model.codom

  app(i::Int)::C = getvalue(model)[i]

  function postcompose(f::FinFunction′)::FinFunction′
    FinFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end

end



# Default constructors
######################

""" 
Default `FinFunction` or `FinDomFunction` from a `AbstractVector` and codom
"""
FinFunction(f::AbstractVector, cod::FinSet; index=false, kw...) = 
  FinFunction(FF(index)(f, cod; kw...))

FinFunction(f::AbstractVector, dom::FinSet, cod::FinSet; index=false, kw...) = 
  dom == FinSet(length(f)) ? FinFunction(f, cod; index, kw...) : error(
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

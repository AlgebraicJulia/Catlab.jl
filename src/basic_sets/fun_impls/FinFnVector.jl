module FinFnVector

export FinFunctionVector, IndexedFinFunctionVector, AbsFinFunctionVector

using StructEquality, DataStructures
using GATlab
import ACSets.Columns: preimage

using ..BasicSets: SetFunction, AbsSet,SetOb, FinSet, ThFinDomFunction, ThFinFunction
using ..FinFunctions:  FinFunction′
using ..FinDomFunctions: FinDomFunction′
import ..BasicSets:  FinFunction, FinDomFunction, is_indexed
using .ThFinDomFunction

# treat indexed and non-indexed cases alike
abstract type AbsFinFunctionVector{C<:AbsSet,T,V} end 

GATlab.getvalue(v::AbsFinFunctionVector) = v.val 

# We do not want equality to distinguish between 
# indexed and non-indexed FinFunctionVectors
Base.hash(f::AbsFinFunctionVector, h::UInt64) = hash((f.val, f.dom, f.codom), h)

Base.:(==)(f::AbsFinFunctionVector, g::AbsFinFunctionVector) = (f.val, f.dom, f.codom) == (g.val, g.dom, g.codom)

""" Implicitly domain is `FinSet(length(v))` Codomain is SetOb."""
struct FinFunctionVector{C<:AbsSet,T,V<:AbstractVector} <: AbsFinFunctionVector{C,T,V}
  val::V
  dom::FinSet
  codom::C
  function FinFunctionVector(val::AbstractVector,codom::C; check=false) where {C<:AbsSet}
    if check 
      for (i,v) in enumerate(val)
        v ∈ codom || error("Bad FinFunctionVector value #$i: $v not in $codom")
      end
    end 
    new{C,eltype(codom),typeof(val)}(val, FinSet(length(val)), codom)
  end
end

"""  Implicitly domain is `FinSet(length(v))` """
struct IndexedFinFunctionVector{C,T,V<:AbstractVector} <: AbsFinFunctionVector{C,T,V}
  val::V
  dom::FinSet
  codom::C
  index::DefaultDict
  """ Create the index cache upon creating the vector """
  function IndexedFinFunctionVector(v, c::C; check=false) where {C<:AbsSet}
    index = DefaultDict{eltype(c), Vector{Int}}(()->[])
    for (i, x) in enumerate(v)
      check && x ∉ c && error("Bad FinFunctionVector value #$i: $x not in $c")
      push!(index[x], i)
    end

    new{C,eltype(c),typeof(v)}(v, FinSet(length(v)), c, index)
  end
end

is_indexed(::IndexedFinFunctionVector) = true

preimage(f::IndexedFinFunctionVector, x) = f.index[x]

FF(i::Bool) = i ? IndexedFinFunctionVector : FinFunctionVector

@instance ThFinFunction{Int,C} [model::AbsFinFunctionVector{FinSet,C,V}] where {C,V} begin

  dom()::FinSet = model.dom

  codom()::FinSet = model.codom

  app(i::Int)::C = model.val[i]

  function postcompose(f::FinFunction′)::FinFunction′
    FinFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end

end

@instance ThFinDomFunction{Int,C} [model::AbsFinFunctionVector{SetOb,C}] where {C} begin

  dom()::FinSet = FinSet(length(getvalue(model)))

  codom()::SetOb = model.codom

  app(i::Int)::C = getvalue(model)[i]

  function postcompose(f::SetFunction)::FinDomFunction
    FinDomFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end

end

function Base.show(io::IO, f::AbsFinFunctionVector)
  Dom = f.codom isa FinSet ? "" : "Dom"
  print(io, "Fin$(Dom)Function($(getvalue(f)), ")
  print(io, getvalue(f.codom))
  is_indexed(f) &&  print(io, ", index=true")
  print(io, ")")
end


# Default constructors
######################
FinFunction(f::AbstractVector; kw...) = FinFunction(f, maximum(f; init=0); kw...
)
FinFunction(f::AbstractVector, cod::Int; kw...) = 
  FinFunction(f, FinSet(cod); kw...)

FinFunction(f::AbstractVector, dom::Int, cod::Int; kw...) = 
  FinFunction(f, FinSet(dom), FinSet(cod); kw...)


FinFunction(f::AbstractVector, cod::FinSet; index=false, kw...) = 
  FinFunction(FF(index)(f, cod; kw...))


FinFunction(f::AbstractVector, dom::FinSet, cod::FinSet; index=false, kw...) = 
    dom == FinSet(length(f)) ? FinFunction(f, cod; index, kw...) : error(
      "Bad domain $dom for vector $f")

FinDomFunction(f::AbstractVector, cod::SetOb; index=false, kw...) = 
  FinDomFunction(FF(index)(f, cod; kw...))

FinDomFunction(f::AbstractVector, cod::Int; kw...) = 
  FinDomFunction(f, FinSet(cod); kw...)

FinDomFunction(f::AbstractVector, dom::Int, cod::Int; kw...) = 
  FinDomFunction(f, FinSet(dom), FinSet(cod); kw...)


FinDomFunction(f::AbstractVector, dom::FinSet, cod::SetOb; index=false, kw...) = 
    dom == FinSet(length(f)) ? FinDomFunction(f, cod; index, kw...) : error(
      "Bad domain $dom for vector $f")
  
end # module

module FinDomFnVector

using StructEquality, DataStructures
using GATlab
import ACSets.Columns: preimage

using ..SetFunctions: SetFunction, dom, codom, SetOb
using ...FinSets: FinSet, FinSetInt
import ..FinDomFunctions:  FinFunction, FinDomFunction, is_indexed, ThFinDomFunction, FinDomFunction′
using .ThFinDomFunction

# treat indexed and non-indexed cases alike
abstract type AbsFinDomFunctionVector{C} end 

GATlab.getvalue(v::AbsFinDomFunctionVector) = v.val 

""" Implicitly domain is `FinSet(length(v))` Codomain is SetOb."""
@struct_hash_equal struct FinDomFunctionVector{C} <: AbsFinDomFunctionVector{C}
  val::AbstractVector
  codom::SetOb
  function FinDomFunctionVector(val::AbstractVector,codom::SetOb; check=false)
    if check 
      for (i,v) in enumerate(val)
        v ∈ codom || error("Bad FinFunctionVector value #$i: $v not in $codom")
      end
    end 
    new{eltype(codom)}(val, codom)
  end
end

"""  Implicitly domain is `FinSet(length(v))` """
@struct_hash_equal struct IndexedFinDomFunctionVector{C} <: AbsFinDomFunctionVector{C}
  val::AbstractVector
  codom::SetOb
  index::DefaultDict
  """ Create the index cache upon creating the vector """
  function IndexedFinDomFunctionVector(v, c::SetOb; check=false)
    index = DefaultDict{eltype(c), Vector{Int}}(()->[])
    for (i, x) in enumerate(v)
      check && x ∉ c && error("Bad FinDomFunctionVector value #$i: $x not in $c")
      push!(index[x], i)
    end

    new{eltype(c)}(v, c, index)
  end
end

is_indexed(::IndexedFinDomFunctionVector) = true

preimage(f::IndexedFinDomFunctionVector, x) = f.index[x]

FF(i::Bool) = i ? IndexedFinDomFunctionVector : FinDomFunctionVector

@instance ThFinDomFunction{Int,C} [model::AbsFinDomFunctionVector{C}] where {C} begin

  dom()::FinSet = FinSet(length(getvalue(model)))

  codom()::SetOb = model.codom

  app(i::Int)::C = getvalue(model)[i]

  # precompose(f::FinFunction) = precompose(model, f)

  function postcompose(f::SetFunction)::FinDomFunction
    FinDomFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end

end

function Base.show(io::IO, f::AbsFinDomFunctionVector)
  print(io, "FinDomFunction($(getvalue(f)), ")
  print(io, f.codom)
  is_indexed(f) &&  print(io, ", index=true")
  print(io, ")")
end


# Default constructors
######################

FinDomFunction(f::AbstractVector, cod::SetOb; index=false, kw...) = 
  FinDomFunction(FF(index)(f, cod; kw...))


FinDomFunction(f::AbstractVector, dom::FinSet, cod::SetOb; index=false, kw...) = 
    dom == FinSet(length(f)) ? FinDomFunction(f, cod; index, kw...) : error(
      "Bad domain $dom for vector $f")
  
end # module
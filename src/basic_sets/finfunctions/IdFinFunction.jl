module IdFinFunction 
export IdentityFinFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage

using ...FinSets
using ..FinFunctions: dom, codom, FinFunction′, ThFinFunction
import ..FinFunctions: FinFunction, is_indexed


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFinFunction{T}
  dom::FinSet
  IdentityFinFunction(d::FinSet) = new{eltype(d)}(d)
end

GATlab.getvalue(i::IdentityFinFunction) = i.dom

# Other methods 
###############

is_indexed(::IdentityFinFunction) = true 

""" Preimage is called on particular values of codom """
preimage(::IdentityFinFunction, x) = [x]

function Base.show(io::IO, f::IdentityFinFunction)
  print(io, "id(")
  print(io, getvalue(f))
  print(io, ")")
end


# FinFunction implementation 
############################


@instance ThFinFunction{T,T} [model::IdentityFinFunction{T}] where T begin

  dom() = getvalue(model)

  codom() = getvalue(model)

  function app(i::T)::T 
    i ∈ dom[model]() || error("$i ∉ $(dom[model]()) for identity function")
    return i
  end

  postcompose(f::FinFunction′)::FinFunction′ = f

end

# Constructors 
##############

function IdentityFinFunction(dom::FinSet, codom::FinSet)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFinFunction(dom)
end

FinFunction(::typeof(identity), arg::FinSet) = FinFunction(IdentityFinFunction(arg))

FinFunction(s::FinSet) = FinFunction(IdentityFinFunction(s))

end # module

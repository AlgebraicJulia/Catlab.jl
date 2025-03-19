module IdFunction 
export IdentityFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction, SetFunction′


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFunction{T}
  dom::SetOb
  IdentityFunction(d::SetOb) = new{eltype(d)}(d)
end

GATlab.getvalue(i::IdentityFunction) = i.dom

# Other methods 
###############

""" Preimage is called on particular values of codom """
preimage(::IdentityFunction, x) = [x]

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  print(io, getvalue(f))
  print(io, ")")
end

# SetFunction implementation 
############################

@instance ThSetFunction{T,T} [model::IdentityFunction{T}] where T begin

  dom() = getvalue(model)

  codom() = getvalue(model)

  function app(i::T)::T 
    i ∈ dom[model]() || error("$i ∉ $(dom[model]()) for identity function")
    return i
  end

  postcompose(f::SetFunction′)::SetFunction′ = f

end

# Constructors 
##############

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

SetFunction(::typeof(identity), arg::SetOb) = SetFunction(IdentityFunction(arg))

SetFunction(s::SetOb) = SetFunction(IdentityFunction(s))

end # module

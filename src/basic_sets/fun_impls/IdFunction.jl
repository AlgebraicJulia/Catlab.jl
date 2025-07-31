module IdFunction 
export IdentityFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage

using ..BasicSets: FinFunction, SetFunction, FinFunction′, ThFinFunction, SetFunction′, ThSetFunction, AbsSet, SetOb, FinSet
import ..BasicSets: FinFunction, SetFunction, is_indexed
using .ThSetFunction


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFunction{T<:AbsSet, D}
  dom::T
  IdentityFunction(d::T) where T<:AbsSet = new{T, eltype(d)}(d)
end

GATlab.getvalue(i::IdentityFunction) = i.dom

# Other methods 
###############

is_indexed(::IdentityFunction) = true 

""" Preimage is called on particular values of codom """
preimage(::IdentityFunction, x) = [x]

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  print(io, getvalue(f))
  print(io, ")")
end


# FinFunction implementation 
############################


@instance ThFinFunction{T,T} [model::IdentityFunction{FinSet, T}] where T begin

  dom()::FinSet = getvalue(model)

  codom()::FinSet = getvalue(model)

  function app(i::T)::T 
    i ∈ dom[model]() || error("$i ∉ $(dom[model]()) for identity function")
    return i
  end

  postcompose(f::FinFunction′)::FinFunction′ = f

end

@instance ThSetFunction{T,T} [model::IdentityFunction{SetOb,T}] where T begin

  dom()::SetOb = getvalue(model)

  codom()::SetOb = getvalue(model)

  function app(i::T)::T 
    i ∈ dom[model]() || error("$i ∉ $(dom[model]()) for identity function")
    return i
  end

  postcompose(f::SetFunction′)::SetFunction′ = f

end

# Constructors 
##############

function IdentityFunction(dom::FinSet, codom::FinSet)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

FinFunction(::typeof(identity), arg::FinSet) = FinFunction(IdentityFunction(arg))

FinFunction(s::FinSet) = FinFunction(IdentityFunction(s))

SetFunction(::typeof(identity), arg::SetOb) = SetFunction(IdentityFunction(arg))

SetFunction(s::SetOb) = SetFunction(IdentityFunction(s))

end # module

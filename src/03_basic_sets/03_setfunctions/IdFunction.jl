module IdFunction 

export IdentityFunction

using StructEquality

using GATlab
import GATlab: getvalue
import ACSets.Columns: preimage

using ..Sets: AbsSet, SetOb
using ..SetFunctions: ThSetFunction, show_domains
import ..SetFunctions: SetFunction


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFunction{T<:AbsSet}
  dom::T
end

# Accessor
##########

getvalue(i::IdentityFunction) = i.dom

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

@instance ThSetFunction{Any, SetFunction, T, T
                       } [model::IdentityFunction{T}] where {T} begin

  dom()::T = getvalue(model)

  codom()::T = getvalue(model)

  app(i::Any)::Any = i

  postcompose(f::SetFunction)::SetFunction = f

end

# Constructors 
##############

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

SetFunction(::typeof(identity), arg::AbsSet) = SetFunction(IdentityFunction(arg))

SetFunction(s::AbsSet) = SetFunction(IdentityFunction(s))

end # module

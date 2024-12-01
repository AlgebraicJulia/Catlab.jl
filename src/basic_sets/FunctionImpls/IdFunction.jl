module IdFunction 

export IdentityFunction

using StructEquality

using GATlab
import GATlab: getvalue
import ACSets.Columns: preimage

using ...Sets: AbsSet, SetOb
using ..SetFunctions: SetFunctionImpl, ThSetFunction, show_domains
import ..SetFunctions: SetFunction


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFunction <: SetFunctionImpl
  dom::AbsSet
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
  show_domains(io, SetFunction(f), codomain=false)
  print(io, ")")
end

# SetFunction implementation 
############################

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::IdentityFunction] begin

  dom()::AbsSet = getvalue(model)

  codom()::AbsSet = getvalue(model)

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

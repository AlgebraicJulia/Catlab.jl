module IdFunction 
export IdentityFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction


""" Identity morphism in **Set**.
"""
@struct_hash_equal struct IdentityFunction
  dom::AbsSet
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

@instance ThSetFunction [model::IdentityFunction] begin

  dom()::AbsSet = getvalue(model)

  codom()::AbsSet = getvalue(model)

  function app(i::Any)::Any 
    i ∈ dom[model]() || error("$i ∉ $(dom[model]()) for identity function")
    return i
  end

  postcompose(f::AbsFunction)::AbsFunction = f

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

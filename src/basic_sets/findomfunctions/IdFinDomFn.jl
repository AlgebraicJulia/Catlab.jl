module IdFinDomFunction 
export IdentityFinDomFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage

using ...BasicSets
using ..FinDomFunctions:  FinDomFunction′, ThFinDomFunction
import ..FinDomFunctions: FinDomFunction, dom, codom, is_indexed


""" Identity heteromorphism between **FinSet** and **Set**.
"""
@struct_hash_equal struct IdentityFinDomFunction{C,D}
  dom::FinSet
  cod::SetOb
  function IdentityFinDomFunction(d::FinSet, c::SetOb) 
    all(x->x ∈ codom, dom) || error("Domain mismatch in identity function: $dom != $codom")
    new{eltype(d), eltype(c)}(d,c)
  end
end

dom(i::IdentityFinDomFunction) = i.dom
codom(i::IdentityFinDomFunction) = i.cod

# Other methods 
###############
is_indexed(::IdentityFinDomFunction) = true
is_epic(::IdentityFinDomFunction) = true


""" Preimage is called on particular values of codom """
preimage(::IdentityFinDomFunction, x) = [x]

function Base.show(io::IO, f::IdentityFinDomFunction)
  print(io, "id(")
  print(io, getvalue(f))
  print(io, ")")
end

# FinDomFunction implementation 
############################

@instance ThFinDomFunction{C,D} [model::IdentityFinDomFunction{C,D}] where {C,D} begin

  dom() = dom(model)

  codom() = codom(model)

  function app(i::C)::D 
    i ∈ dom[model]() || error("$i ∉ $(dom(model)) for identity function")
    return i
  end
  postcompose(f::SetFunction)::FinDomFunction′ = FinDomFunction(model, f)
end

# Constructors 
##############


FinDomFunction(::typeof(identity), arg::FinSet, cod::SetOb) = FinDomFunction(IdentityFinDomFunction(arg, cod))

FinDomFunction(s::FinSet, c::SetOb) = FinDomFunction(IdentityFinDomFunction(s,c))

end # module

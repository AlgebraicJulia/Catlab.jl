module IdFunction 
export IdentityFunction

using StructEquality

import ....Theories: dom, codom
using ..Sets, ..SetFunctions


""" Identity function in **Set**.
"""
@struct_hash_equal struct IdentityFunction{Dom} <: SetFunction{Dom,Dom}
  dom::Dom
end

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

codom(f::IdentityFunction) = f.dom

(f::IdentityFunction)(x) = x

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  SetFunctions.show_domains(io, f, codomain=false)
  print(io, ")")
end

end # module

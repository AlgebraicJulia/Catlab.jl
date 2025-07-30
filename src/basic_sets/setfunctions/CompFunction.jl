module CompFunction
export CompositeFunction

using StructEquality

import ....Theories: dom, codom
using ..Sets, ..SetFunctions

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFunction{Dom,Codom,
    F<:SetFunction{Dom,<:SetOb},G<:SetFunction{<:SetOb,Codom}} <: SetFunction{Dom,Codom}
  fst::F
  snd::G
end
Base.first(f::CompositeFunction) = f.fst
Base.last(f::CompositeFunction) = f.snd

dom(f::CompositeFunction) = dom(first(f))
codom(f::CompositeFunction) = codom(last(f))

(f::CompositeFunction)(x) = f.snd(f.fst(x))

function Base.show(io::IO, f::CompositeFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

end # module

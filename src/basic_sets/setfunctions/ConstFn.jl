module ConstFn
export ConstantFunction

using StructEquality

using ..Sets, ..SetFunctions

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction{T,Value<:T,Dom,Codom<:SetOb{T}} <:
    SetFunction{Dom,Codom}
  value::Value
  dom::Dom
  codom::Codom
end

ConstantFunction(value::T, dom::SetOb) where T =
  ConstantFunction(value, dom, TypeSet{T}())

(f::ConstantFunction)(x) = f.value

end # module

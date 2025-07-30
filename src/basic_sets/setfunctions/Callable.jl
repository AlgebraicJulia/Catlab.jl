module Callable 
export SetFunctionCallable

using StructEquality

using ..Sets, ..SetFunctions

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable{
    T,T′,Dom<:SetOb{T},Codom<:SetOb{T′}} <: SetFunction{Dom,Codom}
  # Field `func` is usually a `Function` but can be any Julia callable.
  func::Any
  dom::Dom
  codom::Codom

  function SetFunctionCallable(f, dom::Dom, codom::Codom) where
      {T,T′,Dom<:SetOb{T},Codom<:SetOb{T′}}
    new{T,T′,Dom,Codom}(f, dom, codom)
  end
end

function (f::SetFunctionCallable{T,T′})(x::T)::T′ where {T,T′}
  f.func(x)
end

function Base.show(io::IO, f::F) where F <: SetFunctionCallable
  SetFunctions.show_type_constructor(io, F)
  print(io, "($(nameof(f.func)), ")
  SetFunctions.show_domains(io, f)
  print(io, ")")
end

end # module


# Identity 
#---------

""" Identity function in **Set**.
"""
@struct_hash_equal struct IdentityFunction <: SetFunctionImpl
  dom::AbsSet
end

getvalue(i::IdentityFunction) = i.dom

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

# dom(s::IdentityFunction) = s.dom # needed for how 'show_domains' works

""" Preimage is called on particular values of codom """
preimage(::IdentityFunction, x) = [x]

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  show_domains(io, SetFunction(f), codomain=false)
  print(io, ")")
end

# SetFunction implementation 

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::IdentityFunction] begin

  dom()::AbsSet = getvalue(model)

  codom()::AbsSet = getvalue(model)

  app(i::Any)::Any = i

  postcompose(f::SetFunction)::SetFunction = f
end

# Constructors 

SetFunction(::typeof(identity), arg::AbsSet) = SetFunction(IdentityFunction(arg))

SetFunction(s::AbsSet) = SetFunction(IdentityFunction(s))
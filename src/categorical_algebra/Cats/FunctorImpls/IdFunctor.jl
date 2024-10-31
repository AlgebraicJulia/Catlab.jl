
""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFunctor{Ob,Hom,T<:AbsCat{Ob,Hom}
                                         } <: FunctorImpl{Ob,Ob,Hom,Hom,T,T}
  dom::T
end

Functor(c::AbsCat) = Functor(IdentityFunctor(c))

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  #show_domains(io, F, codomain=false)
  print(io, ")")
end

@instance ThFunctor{O,O,H,H,H,H,T,T} [model::IdentityFunctor{O,H,T}] where {O,H,T} begin 
  dom() = model.dom

  codom() = model.dom

  ob_map(x::O) = x

  hom_map(x::H) = x
end
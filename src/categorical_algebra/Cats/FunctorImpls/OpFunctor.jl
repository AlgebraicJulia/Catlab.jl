
""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::Functor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFunctor{DO,CO,DH,CH,DG,CG,DC,CC
                                         } <: AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC}
  func::Functor{DO,CO,DH,CH,DG,CG,DC,CC}
end

getvalue(F::OppositeFunctor) = F.func

op(f::Functor) = if getvalue(f) isa OppositeFunctor 
  getvalue(getvalue(f)) # optimization
else 
  Functor(OppositeFunctor(f))
end

@instance ThFunctor{DO,CO,DH,CH,DG,CG,DC,CC} [model::OppositeFunctor{DO,CO,DH,CH,DG,CG,DC,CC}
                                       ] where {DO,CO,DH,CH,DG,CG,DC,CC} begin 
  dom() = op(dom(getvalue(model)))

  codom() = op(codom(getvalue(model)))

  ob_map(x::DO) = ob_map(getvalue(model), x) 

  hom_map(f::DG) = hom_map(getvalue(model), f) 
end

# do_compose(F::OppositeFunctor, G::OppositeFunctor) =
#   OppositeFunctor(do_compose(F.func, G.func))

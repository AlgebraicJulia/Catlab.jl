
""" Composite of functors.
"""
@struct_hash_equal struct CompositeFunctor{AO,BO,CO,AH,BH,CH,AG,BG,CG,AC,BC,CC
                                          } <: AbsFunctorImpl{AO,CO,AH,BH,AG,CG,AC,CC}
  fst::Functor{AO,BO,AH,BH,AG,BG,AC,BC}
  snd::Functor{BO,CO,BH,CH,BG,CG,BC,CC}
end

Base.first(F::CompositeFunctor) = F.fst

Base.last(F::CompositeFunctor) = F.snd

@instance ThFunctor{AO,CO,AH,CH,AG,CG,AC,BC
                    } [model::CompositeFunctor{AO,BO,CO,AH,BH,CH,AG,BG,CG,AC,BC,CC}
                      ] where {AO,BO,CO,AH,BH,CH,AG,BG,CG,AC,BC,CC} begin 
  dom() = dom(first(model))

  codom() = codom(last(model))

  ob_map(x::AO) = ob_map(last(model), ob_map(first(model), x))

  hom_map(x::AG) = hom_map(last(model), hom_map(first(model), x))
end

function Base.show(io::IO, F::CompositeFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end
module CompFunctor 

export CompositeFunctor 

using StructEquality
using GATlab

using ...Categories: Cat
using ..Functors: ThFunctor, Functor

""" Composite of functors.
"""
@struct_hash_equal struct CompositeFunctor{AO,CO,AH,CH}
  fst::Functor
  snd::Functor
  function CompositeFunctor(fst::Functor,snd::Functor)
    dom(snd) == codom(fst) || error("Cannot compose $fst and $snd")
    A, C = dom(fst), codom(snd)
    new{obtype(A), obtype(C), homtype(A), homtype(C)}(fst, snd)
  end
end

# Accessors
###########

Base.first(F::CompositeFunctor) = F.fst

Base.last(F::CompositeFunctor) = F.snd

# Other methods
###############
function Base.show(io::IO, F::CompositeFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end

# ThFunctor interface
####################

@instance ThFunctor{AO,CO,AH,CH,Cat,Cat} [model::CompositeFunctor{AO,CO,AH,CH}
                                     ] where {AO,CO,AH,CH} begin 
  dom() = dom(first(model))

  codom() = codom(last(model))

  ob_map(x::AO) = ob_map(last(model), ob_map(first(model), x))

  hom_map(x::AH) = hom_map(last(model), hom_map(first(model), x))
end


end # module

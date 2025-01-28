module DiagramMonads 

import ......Theories: munit

using ...Cats
using ..Diagrams

# Monads of diagrams
####################

# TODO: Define monad multiplications that go along with the units.

#Sends an object of C to the diagram picking it out.
function munit(::Type{FinDomFunctor}, C::AbsCat, x; shape=nothing)
  if isnothing(shape)
    shape = FinCat(1)
  else
    @assert is_discrete(shape) && length(ob_generators(shape)) == 1
  end
  shape isa FinCatPresentation && 
    return Diagram(FinDomFunctor(Dict(nameof(a)=> x for a in ob_generators(shape)),shape,C))
  FinDomFunctor([x], shape, C)
end

function munit(::Type{DiagramHom}, C::AbsCat, f;
               dom_shape=nothing, codom_shape=nothing, cat=:id)
  if cat == :id 
    d = munit(FinDomFunctor, C, dom(C, f), shape=dom_shape)
    d′= munit(FinDomFunctor, C, codom(C, f), shape=codom_shape)
    j = only(ob_generators(shape(d′)))
    isnothing(dom_shape) ? DiagramHom([Pair(j, f)], d, d′) :
    DiagramHom(Dict(only(ob_generators(dom(diagram(d)))) => Pair(j, f)),d,d′)
  elseif cat == :op 
    f = hom(C, f)
    d = munit(Diagram{op}, C, dom(C, f), shape=dom_shape)
    d′= munit(Diagram{op}, C, codom(C, f), shape=codom_shape)
    j = only(ob_generators(shape(d)))
    isnothing(dom_shape) ? DiagramHom([Pair(j, f)], d, d′) :
       DiagramHom(Dict(only(ob_generators(dom(diagram(d′)))) => Pair(j, f)),d,d′; cat=:op)
  end 
end

end # module

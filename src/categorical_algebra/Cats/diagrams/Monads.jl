
# Monads of diagrams
####################

# TODO: Define monad multiplications that go along with the units.

#Sends an object of C to the diagram picking it out.
function munit(::Type{Diagram{T}}, C::Cat, x; shape=nothing) where T
  if isnothing(shape)
    shape = FinCat(1)
  else
    @assert is_discrete(shape) && length(ob_generators(shape)) == 1
  end
  shape isa FinCatPresentation && 
    return Diagram{T}(FinDomFunctor(Dict(nameof(a)=> x for a in ob_generators(shape)),shape,C))
  Diagram{T}(FinDomFunctor([x], shape, C))
end

function munit(::Type{DiagramHom{T}}, C::Cat, f;
               dom_shape=nothing, codom_shape=nothing) where T
  f = hom(C, f)
  d = munit(Diagram{T}, C, dom(C, f), shape=dom_shape)
  d′= munit(Diagram{T}, C, codom(C, f), shape=codom_shape)
  j = only(ob_generators(shape(d′)))
  isnothing(dom_shape) ? DiagramHom{T}([Pair(j, f)], d, d′) :
   DiagramHom{T}(Dict(only(ob_generators(dom(diagram(d)))) => Pair(j, f)),d,d′)
end
function munit(::Type{DiagramHom{op}}, C::Cat, f;
  dom_shape=nothing, codom_shape=nothing)
f = hom(C, f)
d = munit(Diagram{op}, C, dom(C, f), shape=dom_shape)
d′= munit(Diagram{op}, C, codom(C, f), shape=codom_shape)
j = only(ob_generators(shape(d)))
isnothing(dom_shape) ? DiagramHom{op}([Pair(j, f)], d, d′) :
   DiagramHom{op}(Dict(only(ob_generators(dom(diagram(d′)))) => Pair(j, f)),d,d′)
end

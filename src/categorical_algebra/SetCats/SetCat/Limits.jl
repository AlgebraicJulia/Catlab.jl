module SetLimits 

using .....Theories: dom, codom, id, compose, ⋅
using .....BasicSets, ....Cats
import ....Cats: limit, universal

@cartesian_monoidal_instance SetOb SetFunction

limit(Xs::EmptyDiagram{<:TypeSet}) =
  Limit(Xs, SMultispan{0}(TypeSet(Nothing)))

universal(lim::Terminal{TypeSet{Nothing}}, span::SMultispan{0}) =
  ConstantFunction(nothing, apex(span), ob(lim))

limit(Xs::SingletonDiagram{<:TypeSet}) = limit(Xs, SpecializeLimit())

function limit(Xs::ObjectPair{<:TypeSet})
  X1, X2 = Xs
  X = TypeSet(Tuple{eltype(X1),eltype(X2)})
  π1, π2 = SetFunction(first, X, X1), SetFunction(last, X, X2)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::BinaryProduct{<:TypeSet}, span::Span)
  f, g = span
  SetFunction(x -> (f(x),g(x)), apex(span), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:TypeSet})
  X = TypeSet(Tuple{map(eltype, Xs)...})
  πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(Xs) ]
  Limit(Xs, Multispan(X, πs))
end

function universal(lim::Product{<:TypeSet}, span::Multispan)
  @assert length(cone(lim)) == length(span)
  fs = Tuple(legs(span))
  SetFunction(x -> map(f -> f(x), fs), apex(span), ob(lim))
end

function limit(cospan::Multicospan{<:TypeSet})
  eltype(apex(cospan)) == Nothing ? product(feet(cospan)) :
    error("Pullbacks of TypeSets that are not products are not supported")
end

end # module

module SetCats
export Ob 

using GATlab
using ...Theories: ThCategory
import ...Theories: Ob, dom, codom, id, compose, ⋅, ∘
import ..Categories: show_type_constructor, show_domains


using ...BasicSets, ..Categories, ..FreeDiagrams, ..Limits
import ..Limits: limit, colimit, universal


# Category of sets
##################

""" Category of sets and functions.
"""

@instance ThCategory{SetOb, SetFunction} begin
  dom(f::SetFunction) = f.dom
  codom(f::SetFunction) = f.codom

  id(A::SetOb) = SetFunction(identity, A, A)

  function compose(f::SetFunction, g::SetFunction)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    compose_id(f, g)
  end
end

@inline compose_id(f::SetFunction, g::SetFunction) = do_compose(f, g)
@inline compose_id(f::SetFunction, ::IdentityFunction) = f
@inline compose_id(::IdentityFunction, g::SetFunction) = g
@inline compose_id(f::IdentityFunction, ::IdentityFunction) = f

do_compose(f::SetFunction, g::SetFunction) = CompositeFunction(f, g)
do_compose(f::SetFunction, c::ConstantFunction) =
  ConstantFunction(c.value, dom(f), codom(c))
do_compose(c::ConstantFunction, f::SetFunction) =
  ConstantFunction(f(c.value), dom(c), codom(f))
do_compose(c::ConstantFunction, d::ConstantFunction) =
  ConstantFunction(d.value, dom(c), codom(d))

@cartesian_monoidal_instance SetOb SetFunction

""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
Ob(::TypeCat{T}) where T = TypeSet{T}()

# Limits
########

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

# Colimits
##########

colimit(Xs::SingletonDiagram{<:TypeSet}) = colimit(Xs, SpecializeColimit())

end # module

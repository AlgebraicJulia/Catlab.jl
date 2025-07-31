export KleisliC 

using StructEquality
using GATlab 
using ....BasicSets
using ...Cats 

"""
Compose SetFunctions of the form n -> m+T.
"""
@struct_hash_equal struct KleisliC{T}
  KleisliC(t::Type) = new{t}()
end

@instance ThCategoryExplicitSets{FinSet, CopairedFinDomFunction
                                } [model::KleisliC{T}] where T begin 

  ob_set() = SetOb(FinSet)

  hom_set() = PredicatedSet(FinDomFunction, s -> codom(s) isa EitherSet) |> SetOb

  dom(f::CopairedFinDomFunction)::FinSet = f.D

  codom(f::CopairedFinDomFunction)::FinSet = f.L
  
  """ 
  Because Union{} subtypes all other types, this can compose with any other 
  morphism 
  """
  function id(x::FinSet)::CopairedFinDomFunction
    CopairedFinDomFunction(pure(FinFunction(x), T))
  end

  """
  f: o -> n + T
  g: n -> m + T

  Composite is obtained by applying `f` and then splitting cases:
  if Left(n), then apply g, if Right(T), then use that value.

  The T's need not be exactly equal: we can interpret the T of the composition
  as the larger of the two (if one is a subtype of the other).
  """
  function compose(f::CopairedFinDomFunction, g::CopairedFinDomFunction
                  )::CopairedFinDomFunction
    CopairedFinDomFunction(postcompose(get(f), SetFunction(g)))
  end
end

""" Convert a function n->m into a function n->m+T """
function pure(f::F, T::Type)::FinDomFunction where {
    F<:Union{FinDomFunction, FinFunction}}
  precompose(FinDomFunction(
    x->Left(x), dom(f), either(codom(f), SetOb(T))), f)
end

@instance ThConcreteCategory{FinSet, CopairedFinDomFunction
                                } [model::KleisliC{T}] where T begin

  ob_map(x::FinSet) = SetOb(EitherSet(x, SetOb(T)))
  hom_map(f::CopairedFinDomFunction) = SetFunction(f)
  function lift(f′::AbstractFunction, a::FinSet, b::FinSet)
    f = getvalue(force(f′))
    f isa CopairedFinDomFunction || error(
      "Need SetFunction implementation to be CopairedFinDomFunction, not $f")
    f.D ≃ a || error("Bad dom $(f.D) ≠ $a")
    f.L ≃ b || error("Bad codom $(f.L) ≠ $b")
    f.R ≃ SetOb(T) || error("Bad codom $(f.R) ≠ $T")
    f
  end
end


@instance ThCategoryWithMonicsEpics{FinSet, CopairedFinDomFunction
                                } [model::KleisliC{T}] where T begin

  is_monic(f::CopairedFinDomFunction) = all(x->x isa Left, collect(get(f))) && is_monic(get(f))
  function is_epic(f::CopairedFinDomFunction) 
    collect(codom[model](f)) ⊆ getvalue.(collect(get(f)))
  end
end


"""
Convert a FinDomFunction X -> Left(Y) ∪ Right(Z) which, formally, a is 
just a Kleisli map between FinSets X and Y, into a X -> Left(AttrVar) ∪ Right(z)

Which is just postcomposition with the map X -> ℕ which sends each (implicitly 
ordered set to its canonical ordering.)
"""
function to_attrvars(Y_LR::FinSet)
  Y = getvalue(left(getvalue(Y_LR)))
  FinDomFunction(Dict(y=>AttrVar(i) for (i,y) in enumerate(Y)), 
          Y, SetOb(AttrVar))
end

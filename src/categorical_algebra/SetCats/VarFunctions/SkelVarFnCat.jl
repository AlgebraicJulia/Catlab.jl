export SkelKleisli, pure 

using StructEquality
using GATlab 
using ....BasicSets 
using ...Cats 

"""
Compose SetFunctions of the form n -> m+T.
"""
@struct_hash_equal struct SkelKleisli{T}
  SkelKleisli(t::Type) = new{t}()
end

@instance ThCategoryExplicitSets{FinSetInt, FinDomFunction
                                } [model::SkelKleisli{T}] where T begin 

  ob_set() = ProSetOb(FinSetInt)

  hom_set() = PredicatedSet(FinDomFunction, s -> codom(s) isa EitherSet) |> SetOb

  dom(f::FinDomFunction)::FinSetInt = getvalue(dom(f))

  codom(f::FinDomFunction)::FinSetInt = getvalue(left(getvalue(codom(f))))
  
  """ 
  Because Union{} subtypes all other types, this can compose with any other 
  morphism 
  """
  id(x::FinSetInt)::FinDomFunction = pure(FinDomFunction(FinSet(x)), T)

  """
  f: o -> n + T
  g: n -> m + T

  Composite is obtained by applying `f` and then splitting cases:
  if Left(n), then apply g, if Right(T), then use that value.

  The T's need not be exactly equal: we can interpret the T of the composition
  as the larger of the two (if one is a subtype of the other).
  """
  function compose(f::FinDomFunction, g::FinDomFunction)
    NT, MT, N′ = getvalue.([codom(f), codom(g), dom(g)])
    N,  M, = getvalue.([NT.left, MT.left])

    # Validate
    N isa FinSetInt || error("Bad N $N")
    M isa FinSetInt || error("Bad N $N")
    N == N′ || error("Functions don't kleisli compose: $N ≠ $N′")

    kl(x::Left) = g(getvalue(x))
    kl(x::Right) = x

    FinDomFunction(SetFunction(f, SetFunction(SetFunctionCallable(
      kl, FinSet(N), SetOb(MT))))) # compose
  end
end

""" Convert a function n->m into a function n->m+T """
function pure(f::AbsFunction, T::Type)
  SetFunction(f, SetFunction(SetFunctionCallable(
    Left, codom(f), either(codom(f), SetOb(T))))) |> specialize
end


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

@instance ThCategoryExplicitSets{FinSetInt, CopairedFinDomFunction{T,Int,Int}
                                } [model::SkelKleisli{T}] where T begin 

  ob_set() = SetOb(FinSet)

  hom_set() = PredicatedSet(FinDomFunction, s -> codom(s) isa EitherSet) |> SetOb

  dom(f::CopairedFinDomFunction{T,Int,Int})::FinSetInt = getvalue(f.D)

  codom(f::CopairedFinDomFunction{T,Int,Int})::FinSetInt = getvalue(f.L)
  
  id(x::FinSetInt)::CopairedFinDomFunction{T,Int,Int} = 
    CopairedFinDomFunction(pure(FinFunction(FinSet(x)), T))

  """
  f: o -> n + T
  g: n -> m + T

  Composite is obtained by applying `f` and then splitting cases:
  if Left(n), then apply g, if Right(T), then use that value.

  The T's need not be exactly equal: we can interpret the T of the composition
  as the larger of the two (if one is a subtype of the other).
  """
  function compose(f::CopairedFinDomFunction{T,Int,Int}, 
                   g::CopairedFinDomFunction{T,Int,Int}
                  )::CopairedFinDomFunction{T,Int,Int}
    postcompose(WithModel(f), SetFunction(g)) |> getvalue
  end
end

""" Convert a function n->m into a function n->m+T """
function pure(f::FinFunction, T::Type)::FinDomFunction
  for d in dom(f)
    f(d) isa eltype(codom(f)) || error("Bad $f d $d f(d) $(f(d)) not $(eltype(codom(f)))")
  end

  m_mT = FinDomFunction(x->Left{eltype(codom(f))}(x), codom(f), either(codom(f), SetOb(T))) 

  precompose(m_mT, f)
end


"""
The maps [n]->[m] in our category are FinDomFunctions [n]+[m]+T. To embed these 
maps into Set, we interpret the objects [n] as sets [n]+T and the functions f as 
functions [n]+T -> [m]+T by copairing [f, id(T)].
"""
@instance ThConcreteCategory{FinSetInt, CopairedFinDomFunction{T,Int,Int}
                                } [model::SkelKleisli{T}] where T begin

  ob_map(x::FinSetInt) = SetOb(EitherSet(FinSet(x), SetOb(T)))
  hom_map(f::CopairedFinDomFunction{T,Int,Int}) = 
    SetFunction(f)
    #x->x isa Left ? get(f)(getvalue(x)) : x, 
           #    either(f.D, SetOb(T)), 
           #     codom(get(f)))
  function lift(f′::AbstractFunction, a::FinSetInt, b::FinSetInt)
    f = getvalue(force(f′))
    f isa CopairedFinDomFunction{T, Int, Int} || error(
      "Need SetFunction implementation to be CopairedFinDomFunction, not $f")
    getvalue(f.D) == a || error("Bad dom $(f.D) ≠ $a")
    getvalue(f.L) == b || error("Bad codom $(f.L) ≠ $b")
    f.R == SetOb(T) || error("Bad codom $(f.R) ≠ $T")
    f
  end
end

@instance ThCategoryWithMonicsEpics{FinSetInt, CopairedFinDomFunction{T,Int,Int}
                                } [model::SkelKleisli{T}] where T begin

  is_monic(f::CopairedFinDomFunction{T,Int,Int}) = all(x->x isa Left, collect(get(f))) && is_monic(get(f))
  function is_epic(f::CopairedFinDomFunction{T,Int,Int}) 
    collect(codom[model](f)) ⊆ getvalue.(collect(get(f)))
  end
end

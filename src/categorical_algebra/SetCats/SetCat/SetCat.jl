export Ob 

using GATlab
using ....Theories: ThCategory
import ....Theories: Ob, dom, codom, id, compose, ⋅, ∘


using ....BasicSets, ...Cats
import ...Cats: limit, colimit, universal, do_compose


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


""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
Ob(::TypeCat{T}) where T = TypeSet{T}()



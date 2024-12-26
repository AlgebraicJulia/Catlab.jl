module NatTrans 

export co, Cat2, component, dom_ob, codom_ob, is_natural

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue

using ....Theories: ThCategory2
import .ThCategory2: dom, codom, compose, ⋅, ∘, id, composeH, *
using ..Categories: Cat
using ..Functors: Functor

# Natural transformations
#########################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
@theory ThTransformation begin
  DO::TYPE; CH::TYPE; Fun::TYPE
  dom()::Fun 
  codom()::Fun
  component(x::DO)::CH
end

""" Subtypes of this ought implement the ThTransformation interface """
abstract type NatTransImpl{DO,CH} end

""" Abstract base type for a natural transformation between functors.

A natural transformation ``α: F ⇒ G`` has a domain ``F`` and codomain ``G``
([`dom`](@ref) and [`codom`](@ref)), which are functors ``F,G: C → D`` having
the same domain ``C`` and codomain ``D``. The transformation consists of a
component ``αₓ: Fx → Gx`` in ``D`` for each object ``x ∈ C``, accessible using
[`component`](@ref) or indexing notation (`Base.getindex`).
"""
@struct_hash_equal struct Transformation{DO,CH} 
  impl::NatTransImpl{DO,CH}
  function Transformation(i::NatTransImpl{DO,CH}) where {DO,CH}
    implements(i, ThTransformation) || error("Bad model")
    F, G = ThTransformation.dom[i](), ThTransformation.codom[i]()
    dom(F) == dom(G) || error("Domains don't match")
    codom(F) == codom(G) || error("Codomains don't match")
    obtype(dom(F)) == DO || error("Bad dom ob type")
    homtype(codom(F)) == CH || error("Bad codom hom type")
    new{DO,CH}(i)
  end
end

getvalue(t::Transformation) = t.impl 

# Theory methods 




""" Component of natural transformation.
"""
component(t::Transformation, x::Any) = 
  ThTransformation.component[getvalue(t)](x)

@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

# Implementations
#################

include("NatTransImpls/IdTrans.jl")

@reexport using .IdTrans


# # 2-category of categories
# ##########################

struct Cat2 end 

@instance ThCategory2{Cat,Functor,Transformation} [model::Cat2] begin
  dom(F::Functor) = ThFunctor.dom[getvalue(F)]()
  codom(F::Functor) = ThFunctor.codom[getvalue(F)]()
  id(C::Cat) = Transformation(C)

  function compose(F::Functor, G::Functor)
    compose_id(F, G)
  end

  dom(α::Transformation) = ThTransformation.dom[getvalue(α)]()
  codom(α::Transformation) = ThTransformation.codom[getvalue(α)]()
  id(F::Functor) = Transformation(F)

  function compose(α::Transformation, β::Transformation)
    compose_id(α, β)
  end
  function composeH(α::Transformation, β::Transformation)
    composeH_id(α, β)
  end
  function composeH(α::Transformation, H::Functor)
    composeH_id(α, H)
  end
  function composeH(F::Functor, β::Transformation)
    composeH_id(F, β)
  end
end


# TODO: port over the rest of 2 category code
# # XXX: Is this normalization of identities using multiple dispatch a good idea?
# # Unlike in `Sets`, it doesn't feel great since it requires so much boilerplate.

# @inline compose_id(F::Functor, G::Functor) = do_compose(F, G)
# @inline compose_id(F::Functor, ::IdentityFunctor) = F
# @inline compose_id(::IdentityFunctor, G::Functor) = G
# @inline compose_id(F::IdentityFunctor, ::IdentityFunctor) = F

# @inline compose_id(α::Transformation, β::Transformation) = do_compose(α, β)
# @inline compose_id(α::Transformation, ::IdentityTransformation) = α
# @inline compose_id(::IdentityTransformation, β::Transformation) = β
# @inline compose_id(α::IdentityTransformation, ::IdentityTransformation) = α

# @inline composeH_id(α::Transformation, β::Transformation) = do_composeH(α, β)
# @inline composeH_id(α::Transformation, ::IdIdTransformation) = α
# @inline composeH_id(::IdIdTransformation, β::Transformation) = β
# @inline composeH_id(α::IdIdTransformation, ::IdIdTransformation) = α

# @inline composeH_id(α::Transformation, H::Functor) = do_composeH(α, H)
# @inline composeH_id(α::Transformation, ::IdentityFunctor) = α
# @inline composeH_id(α::IdentityTransformation, H::Functor) =
#   id(compose_id(dom(α), H))
# @inline composeH_id(α::IdentityTransformation, ::IdentityFunctor) = α

# @inline composeH_id(F::Functor, β::Transformation) = do_composeH(F, β)
# @inline composeH_id(::IdentityFunctor, β::Transformation) = β
# @inline composeH_id(F::Functor, β::IdentityTransformation) =
#   id(compose_id(F, dom(β)))
# @inline composeH_id(::IdentityFunctor, β::IdentityTransformation) = β

# do_compose(F::Functor, G::Functor) = CompositeFunctor(F, G)

# @inline function do_composeH(α::Transformation, β::Transformation)
#   do_composeH(α, β, Val{:covariant})
# end
# function do_composeH(α::Transformation, β::Transformation,
#                      ::Type{Val{:covariant}})
#   G, H = codom(α), dom(β)
#   compose_id(composeH_id(α, H), composeH_id(G, β))
# end
# function do_composeH(α::Transformation, β::Transformation,
#                      ::Type{Val{:contravariant}})
#   F, K = dom(α), codom(β)
#   compose_id(composeH_id(F, β), composeH_id(α, K))
# end


# """ Oppositization 2-functor.

# The oppositization endo-2-functor on Cat, sending a category to its opposite, is
# covariant on objects and morphisms and contravariant on 2-morphisms, i.e., is a
# 2-functor ``op: Catᶜᵒ → Cat``. For more explanation, see the
# [nLab](https://ncatlab.org/nlab/show/opposite+category).
# """
# op(C::Cat) = OppositeCat(C)
# op(F::Functor) = OppositeFunctor(F)
# #op(α::Transformation) = OppositeTransformation(α)
# op(C::OppositeCat) = C.cat
# op(F::OppositeFunctor) = F.func
# #op(α::OppositeTransformation) = α.trans

""" 2-cell dual of a 2-category.
"""
function co end


end # module
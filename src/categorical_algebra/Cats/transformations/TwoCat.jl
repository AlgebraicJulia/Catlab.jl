module TwoCat
export co 

using GATlab

import .....Theories: ThCategory2
import .ThCategory2: dom, codom, compose, ⋅, ∘, id, composeH, *

using ...Cats
using ..Transformations 
import ..Transformations: do_compose, do_composeH


# 2-category of categories
##########################

@instance ThCategory2{Cat,Functor,Transformation} begin
  dom(F::Functor) = F.dom
  codom(F::Functor) = F.codom
  id(C::Cat) = IdentityFunctor(C)

  function compose(F::Functor, G::Functor)
    compose_id(F, G)
  end

  dom(α::Transformation) = α.dom
  codom(α::Transformation) = α.codom
  id(F::Functor) = IdentityTransformation(F)

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

# XXX: Is this normalization of identities using multiple dispatch a good idea?
# Unlike in `Sets`, it doesn't feel great since it requires so much boilerplate.

@inline compose_id(F::Functor, G::Functor) = do_compose(F, G)
@inline compose_id(F::Functor, ::IdentityFunctor) = F
@inline compose_id(::IdentityFunctor, G::Functor) = G
@inline compose_id(F::IdentityFunctor, ::IdentityFunctor) = F

@inline compose_id(α::Transformation, β::Transformation) = do_compose(α, β)
@inline compose_id(α::Transformation, ::IdentityTransformation) = α
@inline compose_id(::IdentityTransformation, β::Transformation) = β
@inline compose_id(α::IdentityTransformation, ::IdentityTransformation) = α

@inline composeH_id(α::Transformation, β::Transformation) = do_composeH(α, β)
@inline composeH_id(α::Transformation, ::IdIdTransformation) = α
@inline composeH_id(::IdIdTransformation, β::Transformation) = β
@inline composeH_id(α::IdIdTransformation, ::IdIdTransformation) = α

@inline composeH_id(α::Transformation, H::Functor) = do_composeH(α, H)
@inline composeH_id(α::Transformation, ::IdentityFunctor) = α
@inline composeH_id(α::IdentityTransformation, H::Functor) =
  id(compose_id(dom(α), H))
@inline composeH_id(α::IdentityTransformation, ::IdentityFunctor) = α

@inline composeH_id(F::Functor, β::Transformation) = do_composeH(F, β)
@inline composeH_id(::IdentityFunctor, β::Transformation) = β
@inline composeH_id(F::Functor, β::IdentityTransformation) =
  id(compose_id(F, dom(β)))
@inline composeH_id(::IdentityFunctor, β::IdentityTransformation) = β

do_compose(F::Functor, G::Functor) = CompositeFunctor(F, G)

@inline function do_composeH(α::Transformation, β::Transformation)
  do_composeH(α, β, Val{:covariant})
end
function do_composeH(α::Transformation, β::Transformation,
                     ::Type{Val{:covariant}})
  G, H = codom(α), dom(β)
  compose_id(composeH_id(α, H), composeH_id(G, β))
end
function do_composeH(α::Transformation, β::Transformation,
                     ::Type{Val{:contravariant}})
  F, K = dom(α), codom(β)
  compose_id(composeH_id(F, β), composeH_id(α, K))
end

""" 2-cell dual of a 2-category.
"""
function co end

end 
module TwoCat 
export Cat2, co

using StructEquality 
using GATlab 

using .....Theories: ThCategory2
using ...Categories: Cat 
using ...Functors: Functor 
using ..NatTrans: Transformation

# # 2-category of categories
# ##########################

@struct_hash_equal struct Cat2 end 

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

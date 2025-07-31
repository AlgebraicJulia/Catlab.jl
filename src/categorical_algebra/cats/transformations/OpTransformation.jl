import GATlab: op

#= Not yet needed because the only natural transformations we currently support
#are `FinTransformationMap`, for which can just implement `op` directly.

""" Opposite natural transformation between opposite functors.

Call `op(::Transformation)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeTransformation{C,D,F,G,T<:Transformation{C,D,F,G}} <: Transformation{C,D,F,G}
    # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
    #Transformation{OppositeCat{C},OppositeCat{D},OppositeFunctor{C,D,G},OppositeFunctor{C,D,F}}
  trans::T
end

dom(α::OppositeTransformation) = op(codom(α.trans))
codom(α::OppositeTransformation) = op(dom(α.trans))

component(α::OppositeTransformation, x) = component(α.trans, x)

do_compose(α::OppositeTransformation, β::OppositeTransformation) =
  OppositeTransformation(do_compose(β.trans, α.trans))
do_composeH(α::OppositeTransformation, β::OppositeTransformation) =
  OppositeTransformation(do_composeH(α.trans, β.trans))
do_composeH(F::OppositeFunctor, β::OppositeTransformation) =
  OppositeTransformation(do_composeH(F.func, β.trans))
do_composeH(α::OppositeTransformation, H::OppositeFunctor) =
  OppositeTransformation(do_composeH(α.trans, H.func))
=#

#op(α::Transformation) = OppositeTransformation(α)
#op(α::OppositeTransformation) = α.trans

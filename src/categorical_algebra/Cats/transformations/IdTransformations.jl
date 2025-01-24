module IdTransformations
export IdentityTransformation, IdIdTransformation

using StructEquality

using ...Categories, ...Functors
using ..Transformations
import ..Transformations: component, codom

@struct_hash_equal struct IdentityTransformation{C<:Cat,D<:Cat,Dom<:Functor{C,D}} <:
    Transformation{C,D,Dom,Dom}
  dom::Dom
end

codom(α::IdentityTransformation) = α.dom

function component(α::IdentityTransformation, x)
  F = dom(α)
  id(codom(F), ob_map(F, x))
end

const IdIdTransformation{C<:Cat} = IdentityTransformation{C,C,IdentityFunctor{C}}

end # module

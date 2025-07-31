module IdTrans
export IdentityTransformation

using StructEquality

using GATlab

using ...Cats
using ..Transformations
import ..Transformations: Transformation

@struct_hash_equal struct IdentityTransformation{DO, CH, Fun<:AbsFunctor}
  dom::Fun
  function IdentityTransformation(F::T) where {T<:AbsFunctor} 
    DO,CH = impl_type.(Ref(F), [:DomOb, :CodomHom])
    new{DO, CH, T}(F)
  end
end

# Accessors
###########

GATlab.getvalue(i::IdentityTransformation) = i.dom

# Instance of ThTransformation
##############################

@instance ThTransformation{DO,CH,F,F} [model::IdentityTransformation{DO,CH,F}
                                    ] where {DO,CH,F} begin
  codom()::F = model.dom
  dom()::F = model.dom
  component(x::DO)::CH = let F = dom[model](); id(codom(F), ob_map(F, x)) end
end 

# Convenience constructors
##########################

Transformation(C::Category) = 
  Transformation(IdentityTransformation(Functor(C))) |> validate

Transformation(C::FinCat) = 
  Transformation(IdentityTransformation(FinFunctor(C))) |> validate

Transformation(f::AbsFunctor) = 
  Transformation(IdentityTransformation(f)) |> validate

end # module

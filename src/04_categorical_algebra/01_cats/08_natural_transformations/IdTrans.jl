module IdTrans
export IdentityTransformation

using StructEquality

using GATlab

using ...Categories: Cat
using ...Functors: Functor
using ..NatTrans: ThTransformation

@struct_hash_equal struct IdentityTransformation{DO,CH}
  dom::Functor
  IdentityTransformation(F::Functor) = new{obtype(dom(F)), homtype(codom(F))}(F)
end

# Accessors
###########

GATlab.getvalue(i::IdentityTransformation) = i.dom

# Instance of ThTransformation
##############################

@instance ThTransformation{DO,CH,Functor} [model::IdentityTransformation{DO,CH}
                                          ] where {DO,CH} begin
  codom() = model.dom
  dom() = model.dom
  component(x::DO)::CH = let F = dom[model](); id(codom(F), ob_map(F, x)) end
end 

# Convenience constructors
##########################

IdentityTransformation(C::Cat) = IdentityTransformation(IdentityFunctor(C))

Transformation(f::Functor) = Transformation(IdentityTransformation(f))

Transformation(C::Cat) = Transformation(Functor(C))

end # module

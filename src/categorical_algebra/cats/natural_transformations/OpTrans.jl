module OpTrans 

export OppositeTransformation
using StructEquality
using GATlab

using ...Cats
import ...Cats: op
using ..Transformations
import ..Transformations: Transformation

""" Opposite natural transformation between opposite functors.

Call `op(::Transformation)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeTransformation{DO,CH,DF,CF}
  val::Transformation{DO,CH,DF,CF}
end

GATlab.getvalue(o::OppositeTransformation) = o.val

@instance ThTransformation{DO, CH, DF, CF
                          } [model::OppositeTransformation{DO,CH,DF,CF} 
                            ] where {DO,CH,DF,CF} begin

  dom()::DF = op(codom(getvalue(model)))

  codom()::CF = op(dom(getvalue(model)))

  component(x::DO)::CH = component(getvalue(model), x)
end 

# Constructors 
#-------------

op(f::Transformation) = if getvalue(f) isa OppositeTransformation 
  getvalue(getvalue(f))
else 
  Transformation(OppositeTransformation(f)) |> validate
end

# Note on implementing the oppositization 2-functor:
#----------------------------------------------------
# Not yet needed because the only natural transformations we currently support
# are `FinTransformationMap`, for which can just implement `op` directly.

end # module

module CompFn 

export CompositeFunction

using StructEquality

using GATlab

using ..Sets: AbsSet
using ..SetFunctions: ThSetFunction, dom, codom, postcompose
import ..SetFunctions: SetFunction
using ..IdFunction: IdentityFunction

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFunction{D,C}
  fst::SetFunction{Any,SetFunction,D,<:AbsSet}
  snd::SetFunction{Any,SetFunction,<:AbsSet,C}
end

# Accessors 
###########

Base.first(f::CompositeFunction) = f.fst

Base.last(f::CompositeFunction) = f.snd

# Other methods
###############

function Base.show(io::IO, f::CompositeFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

# SetFunction implementation 
############################

@instance ThSetFunction{Any, SetFunction, D, C} [model::CompositeFunction{D,C}
                                                ] where {D,C} begin

  dom()::D = dom(first(model))
  
  codom()::C = codom(last(model))

  app(i::Any)::Any = last(model)(first(model)(i))

  postcompose(f::SetFunction)::SetFunction = SetFunction(SetFunction(model), f) 
end


# Default SetFunction constructor
#################################

"""
Automatically remove identity functions when creating a composite.
"""
function SetFunction(f::SetFunction, g::SetFunction)
  getvalue(f) isa IdentityFunction && return g 
  getvalue(g) isa IdentityFunction && return f
  SetFunction(CompositeFunction(f,g))
end

end # module

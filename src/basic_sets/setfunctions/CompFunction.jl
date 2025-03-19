module CompFn 

export CompositeFunction

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction, SetFunction′
using ..IdFunction: IdentityFunction

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFunction{D,C}
  fst::SetFunction 
  snd::SetFunction
  CompositeFunction(fst::SetFunction, snd::SetFunction) = 
    new{impl_type(fst,:Dom), impl_type(snd, :Cod)}(fst, snd)
end

Base.first(f::CompositeFunction) = f.fst

Base.last(f::CompositeFunction) = f.snd

function Base.show(io::IO, f::CompositeFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

# SetFunction implementation 
############################

@instance ThSetFunction{D,C} [model::CompositeFunction{D,C}] where {D,C} begin

  dom()::SetOb = dom(first(model))
  
  codom()::SetOb = codom(last(model))

  app(i::D)::C = last(model)(first(model)(i))

  # Create a (biased) nested composite function using constructor below
  postcompose(f::SetFunction′)::SetFunction′ = SetFunction(SetFunction(model), f) 
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

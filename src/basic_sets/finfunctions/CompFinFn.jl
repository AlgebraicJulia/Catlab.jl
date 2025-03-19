module CompFinFn 

export CompositeFinFunction

using StructEquality

using GATlab

using ...FinSets, ..FinFunctions
import ..FinFunctions: dom, codom, FinFunction, FinFunction′, ThFinFunction, is_indexed
using ..IdFinFunction: IdentityFinFunction

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFinFunction{D,C}
  fst::FinFunction 
  snd::FinFunction
  CompositeFinFunction(fst::FinFunction, snd::FinFunction) = 
    new{impl_type(fst,:Dom), impl_type(snd, :Cod)}(fst, snd)
end

Base.first(f::CompositeFinFunction) = f.fst

Base.last(f::CompositeFinFunction) = f.snd

is_indexed(f::CompositeFinFunction) = is_indexed(first(f)) || is_indexed(last(f))

function Base.show(io::IO, f::CompositeFinFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

# FinFunction implementation 
############################

@instance ThFinFunction{D,C} [model::CompositeFinFunction{D,C}] where {D,C} begin

  dom()::FinSet = dom(first(model))
  
  codom()::FinSet = codom(last(model))

  app(i::D)::C = last(model)(first(model)(i))

  # Create a (biased) nested composite function using constructor below
  postcompose(f::FinFunction′)::FinFunction′ = FinFunction(FinFunction(model), f) 
end


# Default FinFunction constructor
#################################

"""
Automatically remove identity functions when creating a composite.
"""
function FinFunction(f::FinFunction, g::FinFunction)
  getvalue(f) isa IdentityFinFunction && return g 
  getvalue(g) isa IdentityFinFunction && return f
  FinFunction(CompositeFinFunction(f,g))
end

end # module

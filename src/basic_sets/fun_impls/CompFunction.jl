module CompFn 

export CompositeFunction

using StructEquality

using GATlab

using ..BasicSets: SetOb, AbsSet, FinSet, AbstractFunction, SetFunction′, 
  IdentityFunction, FinFunction′, ThSetFunction, ThFinFunction
import ..BasicSets: SetFunction, FinFunction, is_indexed
using .ThFinFunction

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.

Type parameters:

D - Julia type of the domain set 
C - Julia type of the codomain set 
DM - Julia type of the implementation of the first function
CM - Julia type of the implementation of the second function
"""
@struct_hash_equal struct CompositeFunction{F<:AbstractFunction,D,C,DM,CM}
  fst::WithModel{DM} 
  snd::WithModel{CM}
  function CompositeFunction(fst::F, snd::F) where F <: AbstractFunction 
    ms = getvalue.([fst, snd])
    new{F, impl_type(fst,:Dom), impl_type(snd, :Cod), typeof(ms[1]), typeof(ms[2])
       }(WithModel.(ms)...)
  end
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

is_indexed(f::CompositeFunction) = is_indexed(getvalue(first(f))) || is_indexed(getvalue(last(f)))

# SetFunction implementation 
############################

# The `postcompose` method here is a bit superfluous. We only use `postcompose` 
# in `force`, which takes a `CompositeFunction` to something which is not a 
# composite function. The only kinds of functions which are `postcomposed` have 
# had `force` called on them already, so these methods are unlikely to ever be 
# called. Nevertheless, the implementation given is reasonable if one really 
# wanted to postcompose a `CompositeFunction` with another function.

@instance ThSetFunction{D,C} [model::CompositeFunction{SetFunction, D, C, DM,CM}
                             ] where {D,C,DM,CM} begin

  dom()::SetOb = dom(first(model))
  
  codom()::AbsSet = codom(last(model))

  app(i::D)::C = app(last(model), app(first(model),i))

  # Create a (biased) nested composite function using constructor below
  postcompose(f::SetFunction′)::SetFunction′ = SetFunction(SetFunction(model), f) 
end

@instance ThFinFunction{D,C} [model::CompositeFunction{FinFunction, D, C, DM, CM}
                             ] where {D,C, DM, CM} begin

  dom()::FinSet = dom(first(model))
  
  codom()::FinSet = codom(last(model))

  app(i::D)::C = 
    app(last(model),app(first(model),i))

  # Create a (biased) nested composite function using constructor below
  postcompose(f::FinFunction′)::FinFunction′ = FinFunction(FinFunction(model), f) 
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

"""
Automatically remove identity functions when creating a composite.
"""
function FinFunction(f::FinFunction, g::FinFunction)
  getvalue(f) isa IdentityFunction && return g 
  getvalue(g) isa IdentityFunction && return f
  FinFunction(CompositeFunction(f,g))
end


end # module

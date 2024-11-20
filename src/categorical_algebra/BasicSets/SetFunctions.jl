module SetFunctions

export SetFunction, SetC, force

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue
import AlgebraicInterfaces: dom, codom
import ACSets.Columns: preimage

using ..Sets

# Theory of SetFunctions
########################

"""
Interface we require any implementation of `SetFunction` to satisfy. We should 
be able to extract a (co)dom, apply the function to inputs, and postcompose.

Often, implementations are naturally postcomposed with another function, because 
this allows one to keep the same structure but just update the values. However,
there are _some_ function implementations which do fundamentally change upon 
postcomposition, such as an `IdentityFunction`. Also, in the case of  
`ConstantFunction`s, one more efficiently represents a postcomposition not by 
mapping over the structure with the same value but by just replacing the
function with another `ConstantFunction`. `postcompose` is only ever called when
using `force` to evaluate a `CompositeFunction`.
"""
@theory ThSetFunction begin
  Any′::TYPE
  Set′::TYPE
  Fun′::TYPE
  dom()::Set′
  codom()::Set′
  app(e::Any′)::Any′
  postcompose(t::Fun′)::Fun′
end

abstract type AbsSetFunction end # ONLY subtyped by SetFunction

""" Any type which subtypes this should implement ThSetFunction """
abstract type SetFunctionImpl <: Model{Tuple{Any, AbsSet, AbsSetFunction}} end

# Wrapper type for models of ThSetFunction
##########################################

""" Generic type for morphism in the category **Set**.

Note: This type would be better called simply `Function` but that name is
already taken by the base Julia type.
"""
@struct_hash_equal struct SetFunction{Dom,Cod} <: AbsSetFunction
  impl::Any 
  function SetFunction(i::SetFunctionImpl)
    implements(i, ThSetFunction) || throw(MethodError("Bad model $i"))
    d = ThSetFunction.dom[i]() |> typeof
    c = ThSetFunction.codom[i]() |> typeof 
    new{d,c}(i)
  end
end

getvalue(s::SetFunction) = s.impl 

# Other constructors
####################

function SetFunction{Dom,Cod}(args...; kw...) where {Dom, Cod}
  res = SetFunction(args...; kw...)
  dom(res) isa Dom || error("Bad dom")
  codom(res) isa Cod || error("Bad dom")
  res
end

function SetFunction{Dom}(args...) where {Dom}
  res = SetFunction(args...)
  dom(res) isa Dom || error("Bad dom")
  res
end

SetFunction(f::SetFunction) = f

# Access the model methods
#-------------------------

dom(s::SetFunction) = ThSetFunction.dom[getvalue(s)]()

codom(s::SetFunction) = ThSetFunction.codom[getvalue(s)]()

(s::SetFunction)(x::Any) = ThSetFunction.app[getvalue(s)](x)

Base.show(io::IO, f::SetFunction) = show(io, getvalue(f)) 

postcompose(f::SetFunction, g::SetFunction) = 
  ThSetFunction.postcompose[getvalue(f)](g)

# Other methods
#--------------

"""
Evaluation of a CompositeFunction. This is where `postcompose` gets used.
"""
function force(s::SetFunction)::SetFunction
  i = getvalue(s) 
  i isa CompositeFunction || return s 
  f, g = force.([first(i), last(i)]) 
  
  # Optimization: we want to precompose w/ `f` rather than postcompose w/ `g`
  getvalue(g) isa ConstantFunction && return SetFunction(
    ConstantFunction(getvalue(getvalue(g)), dom(f), codom(g)))
  
  postcompose(f, g)
end

function show_domains(io::IO, f::SetFunction; domain::Bool=true, 
    codomain::Bool=true, recurse::Bool=true)
  get(io, :hide_domains, false) && return print(io, "…")
  domain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
  domain && codomain && print(io, ", ")
  codomain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
end

# Implementations
#################

include("FunctionImpls/IdFunction.jl")
include("FunctionImpls/CompFunction.jl")
include("FunctionImpls/ConstFn.jl")
include("FunctionImpls/ConstEither.jl")
include("FunctionImpls/PredFn.jl")
include("FunctionImpls/Callable.jl")

@reexport using .IdFunction
@reexport using .CompFn
@reexport using .ConstFn
@reexport using .ConstEitherFn
@reexport using .PredFn
@reexport using .CallableFn

# Category 
##########

@struct_hash_equal struct SetC <: Model{Tuple{AbsSet, SetFunction}} end


# # FinSet wrapper for anything which implements ThFinSet 

# @struct_hash_equal struct SkelFinSet <: Model{Tuple{FinSetInt, FinFunction}} end

@instance ThCategory{AbsSet, SetFunction} [model::SetC] begin
  dom(f::SetFunction) = dom(f)
  codom(f::SetFunction) = codom(f)

  id(A::AbsSet) = SetFunction(A)

  function compose(f::SetFunction, g::SetFunction)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end
end

end # module

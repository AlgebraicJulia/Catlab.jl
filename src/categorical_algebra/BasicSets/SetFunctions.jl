module SetFunctions

export SetFunction, SetFunction, ConstantFunction, SetFunctionCallable, 
       CompositeFunction, IdentityFunction, PredicatedFunction, SetC, force

using StructEquality

using GATlab
import GATlab: getvalue
import AlgebraicInterfaces: dom, codom
import ACSets.Columns: preimage

using ..Sets
import ..Sets: left, right
# import ...Cats.FinFunctors: force

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

const M = Model{Tuple{Any, AbsSet, AbsSetFunction}}

abstract type SetFunctionImpl <: M end

# Functions
###########

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

getvalue(s::SetFunction) = s.impl 

""" Default `dom` overload """
dom(s::SetFunction) = ThSetFunction.dom[getvalue(s)]()

codom(s::SetFunction) = ThSetFunction.codom[getvalue(s)]()

(s::SetFunction)(x::Any) = ThSetFunction.app[getvalue(s)](x)

Base.show(io::IO, f::SetFunction) = show(io, getvalue(f)) 

postcompose(f::SetFunction, g::SetFunction) = 
  ThSetFunction.postcompose[getvalue(f)](g)

SetFunction(f::SetFunction) = f

"""
Evaluation of a CompositFunction. This is where `postcompose` gets used.
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

# Implementations
#################
include("FunctionImpls/Callable.jl")

include("FunctionImpls/IdFunction.jl")

include("FunctionImpls/CompFunction.jl")

include("FunctionImpls/ConstFn.jl")

include("FunctionImpls/ConstEither.jl")

include("FunctionImpls/PredFn.jl")

# Category 
##########

@struct_hash_equal struct SetC <: Model{Tuple{AbsSet, SetFunction}} end

@instance ThCategory{AbsSet, SetFunction} [model::SetC] begin
  dom(f::SetFunction) = dom[model(f)](getvalue(f))
  codom(f::SetFunction) = codom[model(f)](getvalue(f))

  id(A::AbsSet) = SetFunction(A)

  function compose(f::SetFunction, g::SetFunction)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end
end

function show_domains(io::IO, f::SetFunction; domain::Bool=true, 
                      codomain::Bool=true, recurse::Bool=true)
  get(io, :hide_domains, false) && return print(io, "…")
  domain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
  domain && codomain && print(io, ", ")
  codomain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
end

end # module

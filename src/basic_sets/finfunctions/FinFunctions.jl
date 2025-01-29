export FinFunction, FinDomFunction, preimage, is_indexed, specialize,
       is_monic, is_epic, is_iso, AbsFinDomFunction, ensure_indexed

using StructEquality
import ACSets.Columns: preimage, Column
using GATlab

using ..FinSets: AbsSet, FinSet, FinSetInt, SetOb
using ..SetFunctions
import ..SetFunctions: SetFunction
import .ThSetFunction: dom, codom, app, postcompose

# Finite functions
##################
""" Common type for `FinFunction` and `FinDomFunction` """
abstract type AbsFinDomFunction <: AbsFunction end 

GATlab.getvalue(f::AbsFinDomFunction) = f.fun

Base.show(io::IO, f::AbsFinDomFunction) = show(io, getvalue(f))

SetFunction(f::AbsFinDomFunction) = getvalue(f)

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explicitly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

FinFunctions can be constructed with or without an explicitly provided codomain.
If a codomain is provided, by default the constructor checks it is valid.

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
@struct_hash_equal struct FinFunction <: AbsFinDomFunction
  fun::SetFunction 
  function FinFunction(s::SetFunction)
    dom(s) isa FinSet || error("Bad dom $(dom(s))")
    codom(s) isa FinSet || error("Bad codom $(codom(s))")
    new(s)
  end
end

@struct_hash_equal struct FinDomFunction <: AbsFinDomFunction
  fun::SetFunction 
  function FinDomFunction(s::SetFunction)
    dom(s) isa FinSet || error("Bad dom $(dom(s))")
    new(s)
  end
end

dom(model::AbsFinDomFunction)::AbsSet = dom(getvalue(model))

codom(model::AbsFinDomFunction)::AbsSet = codom(getvalue(model))

app(model::AbsFinDomFunction,i::Any) = app(getvalue(model), i)

postcompose(model::AbsFinDomFunction,f::AbsFunction)::AbsFunction = 
  postcompose(getvalue(model), f)

(f::AbsFinDomFunction)(i) = app(f, i)


# These could be made to fail early if ever used in performance-critical areas
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))

is_monic(f::AbsFinDomFunction) = length(dom(f)) == length(Set(values(collect(f))))

is_iso(f::AbsFinDomFunction) = is_monic(f) && is_epic(f)

""" Iterate over image of function """
Base.iterate(f::AbsFinDomFunction, xs...) = iterate(f.(dom(f)), xs...)

Base.length(f::AbsFinDomFunction) = length(dom(f))

Base.eltype(f::AbsFinDomFunction) = eltype(codom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::AbsFinDomFunction, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(getvalue(f)), x) # use cached value
  filter(y -> f(y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

""" A SetFunction is indexed iff its implementation is """
is_indexed(f::SetFunction) = is_indexed(getvalue(f))

is_indexed(f::AbsFinDomFunction) = is_indexed(getvalue(f))


""" If an implementation specifically comes with its own `preimage` method, we 
consider the SetFunction to be indexed """
is_indexed(::T) where T = !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::T) where {T<:AbsFinDomFunction}
  is_indexed(f) && return f
  if getvalue(getvalue(f)) isa FinFunctionVector
    return T(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

ensure_indexed(f::SetFunction) = f

# Specializing
###############
specialize(f::FinFunction) = f 
specialize(f::FinDomFunction) = 
  codom(f) isa FinSet ? FinFunction(getvalue(f)) : f

function specialize(f::SetFunction) 
  if dom(f) isa FinSet 
    (codom(f) isa FinSet ? FinFunction : FinDomFunction)(getvalue(f)) 
  else
    f 
  end
end 

# Identity 
##########
FinFunction(s::FinSet) = FinFunction(SetFunction(s))
FinDomFunction(s::FinSet) = FinDomFunction(SetFunction(s))

# Const 
##########
FinFunction(s::ConstantFunction) = FinFunction(SetFunction(s))
FinDomFunction(s::ConstantFunction) = FinDomFunction(SetFunction(s))

# Callables
###########
FinFunction(s::SetFunctionCallable) = FinFunction(SetFunction(s))

FinDomFunction(s::SetFunctionCallable) = FinDomFunction(SetFunction(s))

FinFunction(f::Function, d::FinSet, c::FinSet) =
  FinFunction(SetFunction(f,d,c))

FinDomFunction(f::Function, d::FinSet, c::AbsSet) =
  FinDomFunction(SetFunction(f,d,c))

# Composites
############
FinFunction(f::CompositeFunction) = FinFunction(SetFunction(f))
FinDomFunction(f::CompositeFunction) = FinDomFunction(SetFunction(f))

function FinFunction(f::AbsFunction, g::AbsFunction) 
  dom(f) isa FinSet || error("Cannot create composite Finfunction $f $g")
  codom(g) isa FinSet || error("Cannot create composite Finfunction $f $g")
  FinFunction(SetFunction(SetFunction(f), SetFunction(g)))
end

function FinDomFunction(f::AbsFunction, g::AbsFunction) 
  dom(f) isa FinSet || error("Cannot create composite Finfunction $f $g")
  FinDomFunction(SetFunction(SetFunction(f), SetFunction(g)))
end

# ACSet Interface
#################
FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(
    Int[c[i] for i in dom], codom
  )

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

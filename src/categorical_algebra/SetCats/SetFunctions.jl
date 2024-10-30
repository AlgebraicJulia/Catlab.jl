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
# import ..FinCats: force

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

# Implementations
#################

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable <: SetFunctionImpl
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::AbsSet
  codom::AbsSet
  function SetFunctionCallable(f, dom::AbsSet, codom::AbsSet)
    !isempty(methods(f)) || error("$f must be callable")
    new(f, dom, codom)
  end
end

getvalue(s::SetFunctionCallable) = s.func

function Base.show(io::IO, f::SetFunctionCallable) 
  print(io, "SetFunction")
  print(io, "($(nameof(f.func)), ")
  show_domains(io, SetFunction(f))
  print(io, ")")
end

# SetFunction implementation

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::SetFunctionCallable] begin
  dom()::AbsSet = model.dom
  codom()::AbsSet = model.codom
  app(i::Any)::Any = getvalue(model)(i)
  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(SetFunctionCallable(  
      i -> f(getvalue(model.func)(i)), model.dom, codom(f)))
end


# Default constructors 

function SetFunction(f::Function, d::AbsSet, c::AbsSet) 
  s = SetFunctionCallable(f, d, c) |> SetFunction
  pred = getvalue(d) isa PredicatedSet || getvalue(c) isa PredicatedSet
  pred ? SetFunction(PredicatedFunction(s)) : s
end

# Identity 
#---------

""" Identity function in **Set**.
"""
@struct_hash_equal struct IdentityFunction <: SetFunctionImpl
  dom::AbsSet
end

getvalue(i::IdentityFunction) = i.dom

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

# dom(s::IdentityFunction) = s.dom # needed for how 'show_domains' works

""" Preimage is called on particular values of codom """
preimage(::IdentityFunction, x) = [x]

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  show_domains(io, SetFunction(f), codomain=false)
  print(io, ")")
end

# SetFunction implementation 

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::IdentityFunction] begin

  dom()::AbsSet = getvalue(model)

  codom()::AbsSet = getvalue(model)

  app(i::Any)::Any = i

  postcompose(f::SetFunction)::SetFunction = f
end

# Constructors 

SetFunction(::typeof(identity), arg::AbsSet) = SetFunction(IdentityFunction(arg))

SetFunction(s::AbsSet) = SetFunction(IdentityFunction(s))

# Composite
#----------

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFunction <: SetFunctionImpl
  fst::SetFunction
  snd::SetFunction
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

# SetFunction implementation 

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::CompositeFunction] begin

  dom()::AbsSet = dom(first(model))
  
  codom()::AbsSet = codom(last(model))

  app(i::Any)::Any = last(model)(first(model)(i))

  postcompose(f::SetFunction)::SetFunction = SetFunction(SetFunction(model), f) 
end

# Default SetFunction model

function SetFunction(f::SetFunction, g::SetFunction)
  getvalue(f) isa IdentityFunction && return g 
  getvalue(g) isa IdentityFunction && return f
  SetFunction(CompositeFunction(f,g))
end

# Constant functions
#-------------------

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction <: SetFunctionImpl
  value::Any
  dom::AbsSet
  codom::AbsSet
  function ConstantFunction(v, d, c)
    v ∈ c || error("Value must be in codom")
    new(v, d, c)
  end
end

ConstantFunction(value::T, dom::AbsSet) where T = 
  ConstantFunction(value, dom, SetOb(T))

getvalue(c::ConstantFunction) = c.value

# SetFunction implementation

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::ConstantFunction] begin
  dom()::AbsSet = model.dom
  
  codom()::AbsSet = model.codom

  app(x::Any)::Any = getvalue(model)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstantFunction(f(getvalue(model)), model.dom, codom(f)))
end

# Default constructors 

SetFunction(value, dom::AbsSet) = SetFunction(ConstantFunction(value, dom))

# ConstEither 
#------------
"""
A map out A + C -> B + C, where we interpret C as constant. Because these use 
EitherSets rather than disjoint sets, any overlap between A and C gets treated 
as constant.
"""
@struct_hash_equal struct ConstEither <: SetFunctionImpl
  fun::SetFunction
  dom::AbsSet
  codom::AbsSet
  function ConstEither(f, d, c)
    ed, ec = getvalue(d), getvalue(c)
    ed isa EitherSet && left(ed) == dom(f) || error("f domain mismatch")
    ec isa EitherSet && left(ec) == codom(f) || error("f codomain mismatch")
    right(ec) == right(ed) || error("EitherSet right sets don't match")
    new(f, d, c)
  end
end

getvalue(c::ConstEither) = c.fun

# SetFunction implementation

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::ConstEither] begin
  dom()::AbsSet = model.dom

  codom()::AbsSet = model.codom

  app(i::Any)::Any = 
    i ∈ right(getvalue(model.codom)) ? i : getvalue(model)(i)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstEither(f(getvalue(model)), model.dom, codom[model](f)))
end


# Predicated function
#--------------------

""" 
Wrapper around `SetFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFunction <: SetFunctionImpl 
  val::SetFunction
end

getvalue(p::PredicatedFunction) = p.val

@instance ThSetFunction{Any, SetOb, SetFunction} [model::PredicatedFunction] begin
  dom()::SetOb = dom(getvalue(model))
  codom()::SetOb = codom(getvalue(model))
  function app(i::Any)::Any
    f = getvalue(model)
    d, c = dom(f), codom(f)
    getvalue(d) isa PredicatedSet && i ∉ d && error("Bad domain input")
    v = f(i)
    getvalue(c) isa PredicatedSet && v ∉ c && error("Bad codomain output")
    v
  end
  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(PredicatedFunction(i -> f(model.func(i)), dom[model](model), codom[model](f)))
end

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

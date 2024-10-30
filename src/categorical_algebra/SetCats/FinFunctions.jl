module FinFunctions 
export FinFunction, FinDomFunction, VarFunction, preimage, is_indexed,
       FinFunctionVector, FinFunctionDict, IndexedFinFunctionVector, 
       is_monic, is_epic, is_iso, AttrVal, AttrC


using StructEquality, DataStructures
import StaticArrays
# using StaticArrays: StaticVector, SVector, SizedVector, similar_type
using GATlab
import GATlab: getvalue

import ACSets.Columns: preimage
import AlgebraicInterfaces: dom, codom

import ....Theories: dom, codom, Ob 

using ..Sets, ..SetFunctions, ..FinSets
using ..Sets: SetImpl
using ..SetFunctions: SetFunctionImpl, ThSetFunction, ConstEither
using ...Cats.Categories: Functor
import ...Cats.FreeDiagrams: left, right
using ...Cats.FinFunctors: FinFunctor, collect_ob
import ..SetFunctions: force

# Finite functions
##################

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

FinFunctions can be constructed with or without an explicitly provided codomain.
If a codomain is provided, by default the constructor checks it is valid.

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
const FinFunction = SetFunction{FinSet,FinSet}

const FinDomFunction = SetFunction{FinSet}


# These could be made to fail early if ever used in performance-critical areas
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))

is_monic(f::FinDomFunction) = length(dom(f)) == length(Set(values(collect(f))))

is_iso(f::FinDomFunction) = is_monic(f) && is_epic(f)

Base.iterate(f::FinDomFunction, xs...) = iterate(f.(dom(f)), xs...)

Base.length(f::FinDomFunction) = length(dom(f))

# Indexing 
##########

""" Preimage of a FinDomFunction """
preimage(f::FinDomFunction, x) = if x ∈ codom(f)
  is_indexed(f) && return preimage(getvalue(f), x) # use cached value
  filter(y -> f(y) == x, collect(dom(f)))
else
  error("Cannot take preimage: $x not found in codomain of $f") 
end

is_indexed(f::SetFunction) = is_indexed(getvalue(f))

is_indexed(::T) where {T<:SetFunctionImpl} = 
  !isempty(methods(preimage, (T, Any)))

""" Try to index the function, if it isn't already """
function ensure_indexed(f::FinDomFunction)
  is_indexed(f) && return f
  if getvalue(f) isa FinFunctionVector
    return FinDomFunction(collect(f), codom(f); index=true)
  end
  f # error("Cannot index $(getvalue(f))")
end

# Implementations
#################

# FinFunctionVector
#------------------
abstract type AbsFinFunctionVector <: SetFunctionImpl end

""" 
Implicitly domain is `FinSet(length(v))`
"""
@struct_hash_equal struct FinFunctionVector <: AbsFinFunctionVector
  val::Vector
  codom::AbsSet
end

"""  Implicitly domain is `FinSet(length(v))` """
@struct_hash_equal struct IndexedFinFunctionVector <: AbsFinFunctionVector
  val::Vector
  codom::AbsSet
  index::DefaultDict
  """ Create the index cache upon creating the vector """
  function IndexedFinFunctionVector(v, c)
    index = DefaultDict{eltype(c), Vector{Int}}(()->[])
    for (i, x) in enumerate(v)
      push!(index[x], i)
    end
    new(v, c, index)
  end
end

preimage(f::IndexedFinFunctionVector, x) = f.index[x]

FF(i::Bool) = i ? IndexedFinFunctionVector : FinFunctionVector

getvalue(f::AbsFinFunctionVector) = f.val

function Base.show(io::IO, f::AbsFinFunctionVector)
  print(io, "Fin")
  f.codom isa FinSet || print(io, "Dom")  
  print(io, "Function($(getvalue(f)), ")
  print(io, f.codom)
  is_indexed(f) &&  print(io, ", index=true")
  print(io, ")")
end

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::T] where {T<:AbsFinFunctionVector} begin
  dom()::AbsSet = FinSet(length(getvalue(model)))
  codom()::AbsSet = model.codom
  app(i::Any)::Any = getvalue(model)[i]
  function postcompose(f::SetFunction)::SetFunction
    FinDomFunction(FF(is_indexed(model))(f.(getvalue(model)), codom(f)))
  end
end

""" 
Default `FinFunction` or `FinDomFunction` from a `AbstractVector` and codom
"""
FinFunction(f::AbstractVector, cod::FinSet; index=false) = 
  FinFunction(FF(index)(f, cod))

FinDomFunction(f::AbstractVector, cod::AbsSet; index=false) = 
  FinDomFunction(FF(index)(f, cod))

const Maybe{T} = Union{T, Nothing}

""" Default `FinFunction` between `FinSetInt`s. """
FinFunction(f::AbstractVector{Int}, cod::Maybe{Int}=nothing; index=false) = 
  FinFunction(f, FinSet(isnothing(cod) ? maximum(f) : cod); index)
  
FinDomFunction(f::AbstractVector, cod::Maybe{Int}=nothing; index=false) = 
  FinFunction(f, isnothing(cod) ? maximum(f) : cod; index)

""" Explicitly pass domain and check it's correct """
FinFunction(f::AbstractVector, dom::Int, cod::Int; index=false) = 
  length(f) == dom ? FinFunction(f, FinSet(cod); index) : error(
    "Mismatched dom=$dom for vector $f ($(length(f)))")

# FinFunctionDict
#----------------

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict <: SetFunctionImpl
  val::Dict
  codom::AbsSet
end

getvalue(f::FinFunctionDict) = f.val

function Base.show(io::IO, f::FinFunctionDict)
  print(io, "Fin")
  f.codom isa FinSet || print(io, "Dom")  
  print(io, "Function($(getvalue(f)), ")
  print(io, f.codom)
  print(io, ")")
end


@instance ThSetFunction{Any, AbsSet, SetFunction} [model::FinFunctionDict] begin
  dom()::AbsSet = FinSet(Set(collect(keys(getvalue(model)))))

  codom()::AbsSet = model.codom

  app(i::Any, )::Any = getvalue(model)[i]

  postcompose(g::SetFunction)::SetFunction = 
    FinDomFunction(FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), 
                                   codom(g)))
end
  
""" Default `FinFunction` from a `AbstractDict`"""
FinFunction(f::AbstractDict) = FinFunction(f, FinSet(Set(values(f))))

""" Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, cod::FinSet) = 
  FinFunction(FinFunctionDict(f, cod))

FinDomFunction(f::AbstractDict, cod::SetOb) = 
  FinDomFunction(FinFunctionDict(f, cod))


# VarFunctions
##############

""" Theory of a category with hetromorphisms """
@theory ThHeteroCat <: ThCategory begin
  @op (⇸) := Het
  Het(dom::Ob, codom::Ob)::TYPE
  compose(f,g)::Het(a,c) ⊣ [(a,b,c)::Ob, f::(a→b), g::(b⇸c)]
  compose(f,g)::Het(a,c) ⊣ [(a,b,c)::Ob, f::(a⇸b), g::(b→c)]
  compose(f,g)::Het(a,c) ⊣ [(a,b,c)::Ob, f::(a⇸b), g::(b⇸c)]
end

# AttrVals 
#---------

@struct_hash_equal struct AttrVal{T}
  val::T
end

function getvalue(a::AttrVal{T})::T where T
  a.val
end

# Sets + T 
#----------

""" Turn some set X into X + T """
either_cod(X::AbsSet, T::Type) = SetOb(EitherSet(X, SetOb(AttrVal{T})))


"""
Check if a set is of the form X + TypeSet{AttrVal{T}}). Return X if so, 
otherwise `nothing`. 
"""
either_cod_inv(s::AbsSet, T::Type) = either_cod_inv(getvalue(s), T)

function either_cod_inv(cod::EitherSet, T::Type)::Union{Nothing, FinSet}
  L, R = getvalue.([left(cod), right(cod)])
  R == TypeSet(AttrVal{T}) || return nothing
  L isa EitherSet && return either_cod_inv(L, T) # nested
  FinSet(L)
end

either_cod_inv(::SetImpl, ::Type) = nothing

""" Take a FinDomFunction X->Y and make it into a function X+T->Y+T """
plus_T_dom(f::FinDomFunction, T::Type) =
  SetFunction(ConstEither(f, either_cod(dom(f), T), either_cod(codom(f), T)))

# VarFunctions 
#-------------
abstract type AbsVarFunction{T} end

# Skip indexing for the time being
preimage(f::AbsVarFunction, v) = [x for x in dom(f) if f(x) == v]

function is_monic(f::AbsVarFunction)
  seen = Set()
  for x in dom(f)
    v = f(x)
    v isa AttrVal && return false 
    v ∈ seen && return false 
    push!(seen, v)
  end
  true
end

is_epic(f::AbsVarFunction) = codom(f) ⊆ collect(f) #XXX: tested?


"""
A VarFunction is a FinDomFunction with a codomain of "+ T" for some type T.

If we treat an ordinary set function, e.g. f: FinSet(2) -> FinSet(3), as a 
VarFunction, we are implicitly treating it as f: FinSet(2) -> FinSet(3) + T

This wraps a SetFunction so that dispatch can automatically use AttrC{T} rather 
than SetC in order to compose them.
"""
@struct_hash_equal struct VarFunction{T} <: AbsVarFunction{T}
  val::FinDomFunction
  function VarFunction{T}(f::FinDomFunction) where {T} 
    isnothing(either_cod_inv(codom(f), T)) && error("Bad cod $(codom(f))")
    new{T}(f)
  end
end

getvalue(f::VarFunction) = f.val

force(s::VarFunction{T}) where T = VarFunction{T}(force(getvalue(s)))

VarFunction{T}(args...) where T = VarFunction{T}(FinDomFunction(args...))

function VarFunction{T}(v::AbstractVector, cod::AbsSet) where T 
  cod = SetOb(EitherSet(cod, SetOb(AttrVal{T})))
  VarFunction{T}(FinDomFunction(FinFunctionVector(v, cod)))
end

(f::VarFunction)(i) = getvalue(f)(i) # regular function on non-AttrVals

(f::VarFunction{T})(v::AttrVal{T}) where T = v # no-op on AttrVals

Base.length(f::VarFunction) = length(getvalue(f))

Base.iterate(f::VarFunction, x...) = iterate(getvalue(f), x...)

# Composite VarFunctions 
#-----------------------

abstract type AbsCompositeVarFunction{T} <: AbsVarFunction{T} end 

left(c::AbsCompositeVarFunction) = c.left 

right(c::AbsCompositeVarFunction) = c.right

@struct_hash_equal struct CompositeVarFunctionL{T} <: AbsCompositeVarFunction{T}
  left::AbsVarFunction{T}
  right::FinDomFunction
  function CompositeVarFunctionL(f::AbsVarFunction{T}, g::FinDomFunction) where T 
    codom(f) == dom(g) || error("Mismatch in composition: $(codom(f)) != $(dom(g))")
    new{T}(f,g)
  end
end 

(f::CompositeVarFunctionL)(i) = let v = left(f)(i); 
  v isa AttrVal ? v : right(f)(v)
end

""" Postcompose a Kleisli morphism with an ordinary one """
function force(s::CompositeVarFunctionL{T})::VarFunction{T} where T
  rght = plus_T_dom(right(s), T)
  VarFunction{T}(force(ThCategory.compose[SetC()](getvalue(left(s)), rght)))
end

@struct_hash_equal struct CompositeVarFunctionR{T} <: AbsCompositeVarFunction{T}
  left::FinDomFunction
  right::AbsVarFunction{T}
  function CompositeVarFunctionR(f::FinDomFunction, g::AbsVarFunction{T}) where T
    codom(f) == dom(g) || error("Mismatch in composition: $(codom(f)) != $(dom(g))")
    new{T}(f,g)
  end
end 

""" Precompose a Kleisli morphism with an ordinary one """
function force(s::CompositeVarFunctionR{T})::VarFunction{T} where T
  VarFunction{T}(force(ThCategory.compose[SetC()](left(s), getvalue(right(s)))))
end

(::CompositeVarFunctionR{T})(i::AttrVal{T}) where T = i

""" Kleisli composition """
(f::CompositeVarFunctionR)(i) = right(f)(left(f)(i))

@struct_hash_equal struct CompositeVarFunctionLR{T} <: AbsCompositeVarFunction{T}
  left::AbsVarFunction{T}
  right::AbsVarFunction{T}
  function CompositeVarFunctionLR(f::AbsVarFunction{T}, g::AbsVarFunction{T}) where T
    codom(f) == dom(g) || error("Mismatch in composition: $(codom(f)) != $(dom(g))")
    new{T}(f,g)
  end
end 

""" Kleisli composition """
(f::CompositeVarFunctionLR)(i) = let v = left(f)(i); 
  v isa AttrVal ? v : right(f)(v)
end

""" Compose two Kleisli morphisms """
function force(s::CompositeVarFunctionLR{T})::VarFunction{T} where T
  f, g = getvalue(force(left(s))), getvalue(force(right(s)))
  g′ = plus_T_dom(g, T)
  VarFunction{T}(ThSetFunction.postcompose[getvalue(f)](g′))
end


# Category of VarFunctions
#-------------------------

@struct_hash_equal struct AttrC{T} <: Model{
  Tuple{FinSet, FinDomFunction, AbsVarFunction{T}}}
end

@instance ThHeteroCat{FinSet, FinDomFunction, AbsVarFunction{T}
                     } [model::AttrC{T}] where T begin
  dom(f::AbsVarFunction{T})::FinSet =
    f isa VarFunction ? dom(getvalue(f)) : dom(left(f))

  function codom(f::AbsVarFunction{T})::FinSet 
    f isa CompositeVarFunctionL && return codom(right) 
    f isa CompositeVarFunctionR && return either_cod_inv(codom(right(f)), T)
    either_cod_inv(codom(getvalue(f)), T)
  end

  id(s::FinSet)::FinDomFunction = id[FinC()](s)

  compose(f::FinDomFunction, g::FinDomFunction)::FinDomFunction = 
    compose[FinC()](f, g)
  
  compose(f::AbsVarFunction{T},g::FinDomFunction; context) =
    CompositeVarFunctionL(f, g)

  compose(f::FinDomFunction, g::AbsVarFunction{T}) = 
    CompositeVarFunctionR(f, g)

  compose(f::AbsVarFunction{T}, g::AbsVarFunction{T}) = 
    CompositeVarFunctionLR(f, g)
end



""" Default model """
dom(f::VarFunction{T}) where T  = dom[AttrC{T}()](f)

codom(f::VarFunction{T}) where T  = codom[AttrC{T}()](f)

# Forgetful functor Cat to Set
Ob(F::FinFunctor{Int}) = FinDomFunction(collect_ob(F), Ob(codom(F)))

end # module

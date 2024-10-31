module VarFunctions 

export VarFunction, AttrVal, AttrC

using StructEquality

using GATlab
import GATlab: getvalue

using ...BasicSets.Sets, ...BasicSets.SetFunctions, ...BasicSets.FinSets, ...BasicSets.FinFunctions
using ...BasicSets.Sets: SetImpl
import ....Theories: dom, codom 
import ...BasicSets.Sets: left, right
using ...BasicSets.SetFunctions: ThSetFunction, ConstEither
import ...BasicSets.FinSets: force
import ...BasicSets.FinFunctions: preimage, is_monic, is_epic


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

end # module

export is_cartesian

using Base.Iterators: flatten
using Reexport

using CompTime
@reexport using ACSets
@reexport using ....ACSetsGATsInterop
using ACSets.Columns
using ACSets.DenseACSets: attrtype_type, datatypes

using GATlab
using ....Graphs.BasicGraphs

using ....Theories
import ....Theories: dom, codom, compose, ⋅, id

using ....BasicSets
import ....BasicSets: FinSet, FinFunction, FinDomFunction, SetOb, SetFunction, TypeSet

using ...Cats, ...SetCats
import ...SetCats: VarSet, VarFunction
using ..ACSetTransformations

# Sets interop
##############

""" Create `SetOb` for object or attribute type of attributed C-set.

For objects, the result is a `FinSet`; for attribute types, a `TypeSet`.
"""
@inline SetOb(X::StructACSet{S,Ts}, type::Symbol) where {S,Ts} =
  set_ob(X, Val{S}, Val{Ts}, Val{type})

SetOb(X::DynamicACSet, type::Symbol) =
  runtime(set_ob, X, X.schema, X.type_assignment, type)

@ct_enable function set_ob(X::ACSet, @ct(S), @ct(Ts), @ct(type))
  @ct_ctrl if type ∈ objects(S)
    FinSet(X, @ct type)
  elseif type ∈ attrtypes(S)
    @ct T = attrtype_instantiation(S,Ts,type)
    TypeSet{@ct T}()
  else
    @ct throw(ArgumentError("$(repr(type)) not in $(objects(S)) or $(attrtypes(S))"))
  end
end

""" Create `FinSet` for object of attributed C-set.
"""
@inline FinSet(X::ACSet, type::Symbol) = FinSets.FinSetInt(nparts(X, type))

""" Create `TypeSet` for object or attribute type of attributed C-set.
"""
@inline TypeSet(::StructACSet{S,Ts}, type::Symbol) where {S,Ts} =
  type_set(Val{S}, Val{Ts}, Val{type})

TypeSet(X::DynamicACSet, type::Symbol) = runtime(type_set, X.schema, X.type_assignment,type)

@ct_enable function type_set(@ct(S), @ct(Ts), @ct(type))
  @ct begin
    T = if type ∈ objects(S)
      Int
    elseif type ∈ attrtypes(S)
      attrtype_instantiation(S,Ts,type)
    else
      throw(ArgumentError("$(repr(type)) not in $(objects(S)) or $(attrtypes(S))"))
    end
    TypeSet{T}()
  end
end

FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(
    Int[c[i] for i in dom], codom
  )

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

"""Runtime error if there are any attributes in the column"""
FinDomFunction(c::Column{Int,Union{AttrVar,T}}, dom, codom) where {T} =
  FinDomFunction(
    T[c[i] for i in dom], codom
  )


""" Create `VarSet` for attribute type of attributed C-set."""
function VarSet(X::ACSet, type::Symbol)
  S = acset_schema(X)
  if type ∈ ob(S) #honestly should probably be an error
    return VarSet{Union{}}(nparts(X,type))
  else 
    return VarSet{attrtype_type(X,type)}(nparts(X,type))
  end
end

function VarFunction(X::ACSet, f::Symbol)
  S = acset_schema(X)
  if f ∈ attrs(S; just_names=true)
    VarFunction(X.subparts[f], parts(X,dom(S,f)), FinSet(nparts(X,codom(S,f))))
  else
    VarFunction(FinFunction(X,f)) #also probably an error
  end
end

VarFunction(c::Column{Int,Union{AttrVar, T}}, dom, codom) where {T} =
  VarFunction{T}([c[i] for i in dom], codom)


""" Create `SetFunction` for morphism or attribute of attributed C-set.

For morphisms, the result is a `FinFunction`; for attributes, a
`FinDomFunction`.
"""
@inline SetFunction(X::StructACSet{S}, name::Symbol) where {S} =
  set_function(X, Val{S}, Val{name})

SetFunction(X::DynamicACSet, name::Symbol)  =
  runtime(set_function,X, acset_schema(X), name)

@ct_enable function set_function(X::SimpleACSet, @ct(S), @ct(name))
  @ct_ctrl if name ∈ objects(S) || name ∈ attrtypes(S)
    SetFunction(identity, SetOb(X, @ct name))
  elseif name ∈ homs(S; just_names=true)
    FinFunction(X.subparts[@ct name], FinSet(X, @ct(dom(S, name))), FinSet(X, @ct(codom(S, name))))
  elseif name ∈ attrs(S; just_names=true)
    FinDomFunction(X, @ct name)
  else
    @ct throw(ArgumentError("$(repr(name)) does not belong to schema $(S)"))
  end
end

""" Create `FinFunction` for morphism of attributed C-set.

Indices are included whenever they exist.
"""
@inline FinFunction(X::StructACSet{S}, name::Symbol) where {S} =
  set_function(X, Val{S}, Val{name})

FinFunction(X::DynamicACSet, name::Symbol)  =
  runtime(set_function,X, acset_schema(X), name)


""" Create `FinDomFunction` for morphism or attribute of attributed C-set.

Indices are included whenever they exist. Unlike the `FinFunction` constructor,
the codomain of the result is always of type `TypeSet`.
"""
@inline FinDomFunction(X::StructACSet{S}, name::Symbol) where {S} =
  fin_dom_function(X, Val{S}, Val{name})

@ct_enable function fin_dom_function(X::SimpleACSet, @ct(S), @ct(name))
  @ct_ctrl if name ∈ objects(S)
    n = nparts(X, @ct name)
    FinDomFunction(1:n, FinSet(n), TypeSet{Int}())
  elseif name ∈ homs(S; just_names=true) || name ∈ attrs(S; just_names=true)
    FinDomFunction(X.subparts[@ct name], FinSet(X, @ct(dom(S, name))), TypeSet(X, @ct(codom(S, name))))
  else
    @ct throw(ArgumentError("$(repr(name)) not in $(objects(S)), $(homs(S)), or $(attrs(S))"))
  end
end


""" C-set → named tuple of sets.
"""
function sets(X::ACSet; S=nothing, Ts=nothing, all::Bool=false,var::Bool=false)
  S = isnothing(S) ? acset_schema(X) : S
  Ts = isnothing(Ts) ? datatypes(X) : Ts
  res = NamedTuple(c => SetOb(X,c) for c in objects(S))
  if all 
    return merge(res, NamedTuple(c => SetOb(X,c) for c in attrtypes(S)))
  elseif var 
    return merge(res, NamedTuple(c => VarSet{attrtype_instantiation(S,Ts,c)}(
      nparts(X,c)) for c in attrtypes(S)))
  else 
    return res
  end 
end

# Category of C-sets
####################

@instance ThCategory{ACSet, ACSetTransformation} begin
  @import Ob, Hom, →

  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::ACSet) = ACSetTransformation(map(id, sets(X; var=true)), X, X)

  # Question: Should we incur cost of checking that codom(β) == dom(α)?
  # If either is Loose, return a Loose
  compose(α::ACSetTransformation, β::ACSetTransformation) =
    ACSetTransformation(map(compose, components(α), components(β)), dom(α), codom(β))
end

@cartesian_monoidal_instance ACSet ACSetTransformation
@cocartesian_monoidal_instance ACSet ACSetTransformation

dom(α::ACSetMorphism) = α.dom
codom(α::ACSetMorphism) = α.codom

compose(α::CSetTransformation, β::CSetTransformation) =
  CSetTransformation(map(compose, components(α), components(β)), dom(α), codom(β))

# Cartesian morphisms of acsets
################################

function is_cartesian_at(f::ACSetTransformation,h::Symbol)
  X,Y = FinDomFunctor(dom(f)),FinDomFunctor(codom(f))
  S = acset_schema(dom(f))
  mor,x,y = h,dom(S,h),codom(S,h)
  s = Span(hom_map(X,mor),f[x])
  c = Cospan(f[y],hom_map(Y,mor))
  L = limit(c)
  f = universal(L,s)
  is_iso(f)
end

"""
    is_cartesian(f,hs)

Checks if an acset transformation `f` is cartesian at the homs in the list `hs`.
Expects the homs to be given as a list of `Symbol`s.
"""
is_cartesian(f,hs=homs(acset_schema(dom(f)),just_names=true)) = 
  all(h->is_cartesian_at(f,h),hs)


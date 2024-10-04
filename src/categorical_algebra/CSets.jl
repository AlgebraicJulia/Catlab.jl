""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetMorphism, 
  ACSetTransformation, CSetTransformation, StructACSetTransformation,
  StructTightACSetTransformation, TightACSetTransformation,
  LooseACSetTransformation, SubACSet, SubCSet,
  components, type_components, force,
  naturality_failures, show_naturality_failures, is_natural, in_bounds,
  abstract_attributes, is_cartesian

using Base.Iterators: flatten
using Base.Meta: quot
using Reexport
using StructEquality

using CompTime
@reexport using ACSets
@reexport using ...ACSetsGATsInterop
using ACSets.Columns
using ACSets.DenseACSets: indices, unique_indices, attr_type, attrtype_type,
  datatypes, constructor

using GATlab
using ...Graphs.BasicGraphs
using ...Theories
import ...Theories: ob, hom, dom, codom, compose, ⋅, id,
  meet, ∧, join, ∨, top, ⊤, bottom, ⊥, ⊕, ⊗

using ..FreeDiagrams, ..Limits, ..Subobjects, ..Sets, ..FinSets, ..FinCats
using ..FinSets: VarFunction, LooseVarFunction, IdentityFunction, VarSet, AbsVarFunction
import ..Limits: limit, colimit, universal
import ..Subobjects: Subobject, implies, ⟹, subtract, \, negate, ¬, non, ~
import ..Sets: SetOb, SetFunction, TypeSet
using ..Diagrams: Diagram, diagram
import ..FinSets: FinSet, FinFunction, FinDomFunction, force, predicate, 
                  is_monic, is_epic, preimage
import ..FinCats: FinDomFunctor, components, is_natural

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


# Categories interop
####################

# ACSets as set-valued FinDomFunctors.

# TODO: We should wrap `SchemaDescType` instead of creating a presentation.
const ACSetDomCat = FinCats.FinCatPresentation{
  Symbol, Union{FreeSchema.Ob,FreeSchema.AttrType},
  Union{FreeSchema.Hom,FreeSchema.Attr,FreeSchema.AttrType}}

""" Wrapper type to interpret attributed C-set as a functor.
"""
@struct_hash_equal struct ACSetFunctor{ACS<:ACSet} <:
    Functor{ACSetDomCat,
            TypeCat{Union{FinSet,VarSet},
                    Union{VarFunction,FinDomFunction{Int}}}}
  acset::ACS
end
FinDomFunctor(X::ACSet) = ACSetFunctor(X)
ACSet(X::ACSetFunctor) = X.acset

function hasvar(X::ACSet,x) 
  s = acset_schema(X)
  (x∈ attrs(acset_schema(X),just_names=true) && hasvar(X,codom(s,x))) || 
  x∈attrtypes(acset_schema(X)) && nparts(X,x)>0
end
hasvar(X::ACSet) = any(o->hasvar(X,o), attrtypes(acset_schema(X)))
hasvar(X::ACSetFunctor,x) = hasvar(X.acset,x)
hasvar(X::ACSetFunctor) = hasvar(X.acset)


dom(F::ACSetFunctor) = FinCat(Presentation(ACSet(F)))

#not clear this couldn't just always give the Vars
function codom(::ACSetFunctor)
  TypeCat{Union{SetOb,VarSet},Union{FinDomFunction{Int},VarFunction}}()
  # hasvar(F) ? TypeCat{Union{SetOb,VarSet},Union{FinDomFunction{Int},VarFunction}}() :
  #   TypeCat{SetOb,FinDomFunction{Int}}()
end

function Categories.do_ob_map(F::ACSetFunctor, x)
  S = acset_schema(F.acset)
  Symbol(x) ∈ ob(S) && return SetOb(F.acset, functor_key(x))
  Symbol(x) ∈ attrtypes(S) && return VarSet(F.acset, functor_key(x))
  error("Bad object $S $x")
end
function Categories.do_hom_map(F::ACSetFunctor, x)
  S = acset_schema(F.acset)
  kx = functor_key(x)
  Symbol(kx) ∈ homs(S; just_names=true) && return FinFunction(F.acset, kx)
  Symbol(kx) ∈ attrs(S; just_names=true) && return VarFunction(F.acset, kx)
  error("Bad hom $S $x")
end 

functor_key(x) = x
functor_key(expr::GATExpr{:generator}) = first(expr)

# Set-valued FinDomFunctors as ACSets.
(T::Type{ACS})(F::Diagram) where ACS <: ACSet = F |> diagram |> T
function (::Type{ACS})(F::FinDomFunctor) where ACS <: ACSet
  X = if ACS isa UnionAll
    pres = presentation(dom(F))
    ACS{(strip_attrvars(eltype(ob_map(F, c))) for c in generators(pres, :AttrType))...}()
  else
    ACS()
  end
  copy_parts!(X, F)
  return X
end
strip_attrvars(T) = T
strip_attrvars(::Type{Union{AttrVar, T}}) where T = T

""" Copy parts from a set-valued `FinDomFunctor` to an `ACSet`.
"""
function ACSetInterface.copy_parts!(X::ACSet, F::FinDomFunctor)
  pres = presentation(dom(F))
  added = Dict(Iterators.map(generators(pres, :Ob)) do c
    c = nameof(c)
    c => add_parts!(X, c, length(ob_map(F, c)::FinSet{Int}))
  end)
  for f in generators(pres, :Hom)
    dom_parts, codom_parts = added[nameof(dom(f))], added[nameof(codom(f))]
    set_subpart!(X, dom_parts, nameof(f), codom_parts[collect(hom_map(F, f))])
  end
  for f in generators(pres, :Attr)
    cd = nameof(codom(f))
    dom_parts = added[nameof(dom(f))]
    F_of_f = collect(hom_map(F,f))
    n_attrvars_present = nparts(X, cd)
    n_attrvars_needed = maximum(map(x->x.val,filter(x->x isa AttrVar,F_of_f)),init=0)
    add_parts!(X,cd,n_attrvars_needed-n_attrvars_present)
    set_subpart!(X, dom_parts, nameof(f), F_of_f)
  end
  added
end

# C-set transformations
#######################

""" Common type for `ACSetTransformation` and `CSetTransformation`.
"""
abstract type ACSetMorphism{Dom,Codom} end


""" Transformation between attributed C-sets.

Homomorphisms of attributed C-sets generalize homomorphisms of C-sets
([`CSetTransformation`](@ref)), which you should understand before reading this.

A *homomorphism* of attributed C-sets with schema S: C ↛ A (a profunctor) is a
natural transformation between the corresponding functors col(S) → Set, where
col(S) is the collage of S. When the components on attribute types, indexed by
objects of A, are all identity functions, the morphism is called *tight*; in
general, it is called *loose*. With this terminology, acsets on a fixed schema
are the objects of an ℳ-category (see `Catlab.Theories.MCategory`). Calling
`ACSetTransformation` will construct a tight or loose morphism as appropriate,
depending on which components are specified.

Since every tight morphism can be considered a loose one, the distinction
between tight and loose may seem a minor technicality, but it has important
consequences because limits and colimits in a category depend as much on the
morphisms as on the objects. In particular, limits and colimits of acsets differ
greatly depending on whether they are taken in the category of acsets with tight
morphisms or with loose morphisms. Tight morphisms suffice for many purposes,
including most applications of colimits. However, when computing limits of
acsets, loose morphisms are usually preferable. For more information about
limits and colimits in these categories, see [`TightACSetTransformation`](@ref)
and [`LooseACSetTransformation`](@ref).
"""
abstract type ACSetTransformation{Dom,Codom} <: ACSetMorphism{Dom,Codom} end

""" Tight transformation between attributed C-sets.

The category of attributed C-sets and tight homomorphisms is isomorphic to a
slice category of C-Set, as explained in our paper "Categorical Data Structures
for Technical Computing". Colimits in this category thus reduce to colimits of
C-sets, by a standard result about slice categories. Limits are more complicated
and are currently not supported.

For the distinction between tight and loose, see [`ACSetTranformation`](@ref).
"""
abstract type TightACSetTransformation{Dom,Codom} <:
  ACSetTransformation{Dom,Codom} end

""" Loose transformation between attributed C-sets.

Limits and colimits in the category of attributed C-sets and loose homomorphisms
are computed pointwise on both objects *and* attribute types. This implies that
(co)limits of Julia types must be computed. Due to limitations in the
expressivity of Julia's type system, only certain simple kinds of (co)limits,
such as products, are supported.

Alternatively, colimits involving loose acset transformations can be constructed
with respect to explicitly given attribute type components for the legs of the
cocone, via the keyword argument `type_components` to `colimit` and related
functions. This uses the universal property of the colimit. To see how this
works, notice that a diagram of acsets and loose acset transformations can be
expressed as a diagram D: J → C-Set (for the C-sets) along with another diagram
A: J → C-Set (for the attribute sets) and a natural transformation α: D ⇒ A
(assigning attributes). Given a natural transformation τ: A ⇒ ΔB to a constant
functor ΔB, with components given by `type_components`, the composite
transformation α⋅τ: D ⇒ ΔB is a cocone under D, hence factors through the
colimit cocone of D. This factoring yields an assigment of attributes to the
colimit in C-Set.

For the distinction between tight and loose, see [`ACSetTranformation`](@ref).
"""
abstract type LooseACSetTransformation{Dom,Codom} <:
  ACSetTransformation{Dom,Codom} end

components(α::ACSetMorphism) = α.components
force(α::ACSetMorphism) = map_components(force, α)

# Dynamic ACSet transformations

@struct_hash_equal struct DynamicTightACSetTransformation <:
    TightACSetTransformation{ACSet,ACSet}
  components::NamedTuple
  dom::ACSet
  codom::ACSet
  function DynamicTightACSetTransformation(components, X, Y) 
    S = acset_schema(X)
    components = coerce_components(S,components,X,Y)
    new(components, X, Y)
  end
end

@struct_hash_equal struct DynamicLooseACSetTransformation <:
    LooseACSetTransformation{ACSet,ACSet}
  components::NamedTuple
  type_components::NamedTuple
  dom::ACSet
  codom::ACSet
end

# Struct ACSet transformations

@struct_hash_equal struct StructTightACSetTransformation{
    S <: TypeLevelSchema, Comp <: NamedTuple, Dom <: StructACSet{S},
    Codom <: StructACSet{S}} <: TightACSetTransformation{Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom  

  function StructTightACSetTransformation{S}(components, X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    components = coerce_components(S,components,X,Y)
    new{S,typeof(components),Dom,Codom}(components, X, Y)
  end
end


""" Transformation between C-sets.

Recall that a C-set homomorphism is a natural transformation: a transformation
between functors C → Set satisfying the naturality axiom for every morphism, or
equivalently every generating morphism, in C.

This data type records the data of a C-set transformation. Naturality is not
strictly enforced but is expected to be satisfied. It can be checked using the
function [`is_natural`](@ref).

If the schema of the dom and codom has attributes, this has the semantics of 
being a valid C-set transformation on the combinatorial data alone (including 
attribute variables, if any).
"""
abstract type CSetTransformation{Dom,Codom} <: ACSetMorphism{Dom,Codom} end

@struct_hash_equal struct  StructCSetTransformation{
    S <: TypeLevelSchema, Comp <: NamedTuple, Dom <: StructACSet{S},
    Codom <: StructACSet{S}} <: CSetTransformation{Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom  

  function StructCSetTransformation{S}(components, X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    components = coerce_components(S,components,X,Y)
    new{S,typeof(components),Dom,Codom}(components, X, Y)
  end
end

@struct_hash_equal struct DynamicCSetTransformation <: CSetTransformation{ACSet,ACSet}
  components::NamedTuple
  dom::ACSet
  codom::ACSet
  function DynamicCSetTransformation(components, X, Y) 
    S = acset_schema(X)
    components = coerce_components(S,components,X,Y)
    new(components, X, Y)
  end
end

CSetTransformation(f::StructTightACSetTransformation{S}) where S = 
  StructCSetTransformation{S}(components(f), dom(f), codom(f))
CSetTransformation(f::DynamicTightACSetTransformation) = 
  DynamicCSetTransformation(components(f), dom(f), codom(f))

CSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where S =
  StructCSetTransformation{S}(components, X, Y)
CSetTransformation(X::StructACSet{S}, Y::StructACSet{S}; components...) where S =
  StructCSetTransformation{S}((; components...), X, Y)

TightACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where S =
  StructTightACSetTransformation{S}(components, X, Y)

# Component coercion

function coerce_components(S, components, X::ACSet{<:PT}, Y) where PT
  @assert keys(components) ⊆ objects(S) ∪ attrtypes(S)
  kw = Dict(map(types(S)) do c  
    c => PT <: MarkAsDeleted ? (dom_parts=parts(X,c), codom_parts=parts(Y,c)) : (;)
  end)
  ocomps = NamedTuple(map(objects(S)) do c
    c => coerce_component(c, get(components, c, 1:0), 
                          maxpart(X,c), maxpart(Y,c); kw[c]...)
  end)
  acomps = NamedTuple(map(attrtypes(S)) do c
    c => coerce_attrvar_component(c, get(components, c, 1:0), 
          TypeSet(X, c), TypeSet(Y, c), maxpart(X,c), maxpart(Y,c); kw[c]...)
  end)
  return merge(ocomps, acomps)
end 
  
# Enforces that function has a valid domain (but not necessarily codomain)
function coerce_component(ob::Symbol, f::FinFunction{Int,Int},
                          dom_size::Int, codom_size::Int; kw...)
  if haskey(kw, :dom_parts)
    !any(i -> f(i) == 0, kw[:dom_parts]) # check domain of mark as deleted
  else                         
    length(dom(f)) == dom_size # check domain of dense parts
  end || error("Domain error in component $ob")
  return f 
end

coerce_component(ob::Symbol, f::T, dom_size::Int, codom_size::Int; kw...) where {T<:Integer} =
  error("Scalar component for $ob not allowed; " *
  "this is probably from a scalar component in an ACSetTransformation, please use a vector")

coerce_component(::Symbol, f::T, dom_size::Int, codom_size::Int; kw...) where {T<:AbstractVector{<:Integer}}=
  FinFunction(f, dom_size, codom_size; kw...)

function coerce_attrvar_component(
    ob::Symbol, f::AbstractVector,::TypeSet{T}, ::TypeSet{T},
    dom_size::Int, codom_size::Int; kw...) where {T}
  e = "Domain error in component $ob variable assignment $(length(f)) != $dom_size"
  length(f) == dom_size || error(e)
  return VarFunction{T}(f, FinSet(codom_size))
end

function coerce_attrvar_component(
    ob::Symbol, f::VarFunction,::TypeSet{T},::TypeSet{T},
    dom_size::Int, codom_size::Int; kw...) where {T}
  length(f.codom) == codom_size || error(
    "Codomain error in component $ob: $(f.fun.codom)!=$codom_size")
  return f
end

function coerce_attrvar_component(
    ob::Symbol, f::LooseVarFunction,d::TypeSet{T},cd::TypeSet{T′},
    dom_size::Int, codom_size::Int; kw...) where {T,T′}
  length(dom(f.fun)) == dom_size || error("Domain error in component $ob")
  length(f.codom) == codom_size || error("Codomain error in component $ob: $(f.fun.codom)!=$codom_size")
  # We do not check types (equality is too strict)
  # dom(f.loose) == d || error("Dom of type comp mismatch $(dom(f.loose)), $d")
  # codom(f.loose) == cd || error("Codom of type comp mismatch $(codom(f.loose)), $cd")
  return f
end

"""Coerce an arbitrary julia function to a LooseVarFunction assuming no variables"""
function coerce_attrvar_component(ob::Symbol, f::Function, d::TypeSet{T},cd::TypeSet{T′},
  dom_size::Int, codom_size::Int; kw...) where {T,T′}
  dom_size == 0 || error("Cannot specify $ob component with $f with $dom_size domain variables")
  coerce_attrvar_component(ob, LooseVarFunction{T,T′}([], f, FinSet(codom_size)), 
                           d, cd, dom_size,codom_size)
end

function Base.getindex(α::ACSetMorphism, c) 
  get(α.components, c) do
    c ∈ attrtypes(acset_schema(dom(α))) || error("No object or attribute type with name $c")
    SetFunction(identity, TypeSet(dom(α),c), TypeSet(codom(α),c))
  end
end

map_components(f, α::ACSetMorphism) =
  ACSetTransformation(map(f, components(α)), dom(α), codom(α))

showname(::ACSetTransformation) = "ACSetTransformation"
showname(::CSetTransformation) = "CSetTransformation"
function Base.show(io::IO, α::ACSetMorphism)
  print(io, "$(showname(α))(")
  show(io, components(α))
  print(io, ", ")
  Categories.show_domains(io, α)
  print(io, ")")
end

@struct_hash_equal struct StructLooseACSetTransformation{
    S <: TypeLevelSchema, Comp <: NamedTuple, Dom <: StructACSet{S}, 
    Codom <: StructACSet{S}} <: LooseACSetTransformation{Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom

  function StructLooseACSetTransformation{S}(components, X::Dom, Y::Codom) where
        {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
      components = coerce_components(S,components,X,Y)
      new{S,typeof(components),Dom,Codom}(components, X, Y)
    end
end

type_components(α::StructLooseACSetTransformation{S}) where S =
  NamedTuple(c => α.components[c] for c in attrtypes(S))

const StructACSetTransformation{S,C,X,Y} = 
  Union{StructLooseACSetTransformation{S,C,X,Y}, 
        StructTightACSetTransformation{S,C,X,Y}}


"""Move components as first argument"""
ACSetTransformation(X::ACSet, Y::ACSet; components...) =
  ACSetTransformation((; components...), X, Y)
      
ACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where {S} = 
  _ACSetTransformation(Val{S},components,X,Y,Val{true}) 
ACSetTransformation(components, X::DynamicACSet, Y::DynamicACSet) = 
  runtime(_ACSetTransformation, X.schema, components, X,Y,false)

@ct_enable function _ACSetTransformation(@ct(S), components, X,Y,@ct(is_struct))
  ocomps = NamedTuple(filter(∈(objects(S))∘first, pairs(components)))
  acomps = NamedTuple(filter(∈(attrtypes(S))∘first, pairs(components)))
  length(ocomps) + length(acomps) == length(components) ||
    error("Not all names in $(keys(components)) are objects or attribute types")
  is_tight = true  # we do this with a `for` loop (not `all`) because comptime
  for a in acomps 
    if a isa Function 
      is_tight = false
    elseif a isa LooseVarFunction && !(a.loose isa IdentityFunction)
      is_tight  = false
    elseif a isa Union{VarFunction, AbstractVector}
    else 
      error("Unexpected type for attrtype component of ACSetTransformation")
    end 
  end
  if is_tight
    T = is_struct ? StructTightACSetTransformation{S} : DynamicTightACSetTransformation
    return T(merge(ocomps,acomps), X, Y)
  else
    T = is_struct ? StructLooseACSetTransformation{S} : DynamicLooseACSetTransformation
    return T(merge(ocomps,acomps), X, Y)
  end
end

function LooseACSetTransformation(components, type_components, X::ACSet, Y::ACSet)
  comps = Dict{Symbol,Any}(pairs(components))                     
  for (k,v) in collect(pairs(type_components))
    !haskey(components, k) || isempty(components[k]) || error("$k given as component and type_component")
    nx, ny = [nparts(x,k) for x in [X,Y]]
    nx == 0 || error("Cannot specify $k via a function with $nx vars present")
    T, T′ = [attrtype_type(x, k) for x in [X,Y]]
    if isnothing(v)
      T′ == Nothing || error("No component $k :: $T -> $T′")
      setfun = SetFunction(_->nothing, TypeSet(T),TypeSet(T′))
    else 
      setfun = v isa SetFunction ? v : SetFunction(v,TypeSet(T),TypeSet(T′))
    end 
    comps[k] = LooseVarFunction{T,T′}([],setfun,FinSet(ny))
  end  
  ACSetTransformation(comps, X, Y)
end 

function coerce_type_component(type::Symbol, f::SetFunction,
                               dom_type::Type, codom_type::Type)
  dom_type <: eltype(dom(f)) || error("Domain error in component $type")
  eltype(codom(f)) <: codom_type || error("Codomain error in component $type")
  return f
end
function coerce_type_component(type::Symbol, ::Nothing,
                               dom_type::Type, codom_type::Type)
  codom_type == Nothing || error("Codomain error in component $type")
  ConstantFunction(nothing, TypeSet(dom_type))
end
coerce_type_component(type::Symbol, f, dom_type::Type, codom_type::Type) =
  SetFunction(f, TypeSet(dom_type), TypeSet(codom_type))
  
"""
Check naturality condition for a purported ACSetTransformation, α: X→Y. 
For each hom in the schema, e.g. h: m → n, the following square must commute:

```text
     αₘ
  Xₘ --> Yₘ
Xₕ ↓  ✓  ↓ Yₕ
  Xₙ --> Yₙ
     αₙ
```

You're allowed to run this on a named tuple partly specifying an ACSetTransformation,
though at this time the domain and codomain must be fully specified ACSets.
"""
function is_natural(α::LooseACSetTransformation) 
  is_natural(dom(α), codom(α), α.components, type_components(α))
end
function is_natural(α::ACSetMorphism)
  is_natural(dom(α), codom(α), α.components)
end

is_natural(dom, codom, comps...) =
  all(isempty, last.(collect(naturality_failures(dom, codom, comps...))))

"""
Returns a dictionary whose keys are contained in the names in `arrows(S)`
and whose value at `:f`, for an arrow `(f,c,d)`, is a lazy iterator
over the elements of X(c) on which α's naturality square
for f does not commute. Components should be a NamedTuple or Dictionary
with keys contained in the names of S's morphisms and values vectors or dicts
defining partial functions from X(c) to Y(c).
"""
function naturality_failures(X, Y, comps)
  type_comps = Dict(attr => SetFunction(identity, SetOb(X,attr), SetOb(X,attr)) 
                    for attr in attrtype(acset_schema(X)))
  naturality_failures(X, Y, comps, type_comps)
end
function naturality_failures(X, Y, comps, type_comps)
  S = acset_schema(X)
  Fun = Union{SetFunction, VarFunction, LooseVarFunction}
  comps = Dict(a => isa(comps[a],Fun) ? comps[a] : FinDomFunction(comps[a])  
               for a in keys(comps))
  type_comps = Dict(a => isa(type_comps[a], Fun) ? type_comps[a] : 
                        SetFunction(type_comps[a],TypeSet(X,a),TypeSet(Y,a)) 
                    for a in keys(type_comps))
  α(o::Symbol, i::AttrVar) = comps[o](i)
  α(o::Symbol, i::Any) = o ∈ ob(S) ? comps[o](i) : type_comps[o](i)
  ks = union(keys(comps), keys(type_comps))
  arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, arrows(S))
  ps = Iterators.map(arrs) do (f,c,d)
    Pair(f,
    Iterators.map(i->(i, Y[α(c, i), f], α(d, X[i, f])),
      Iterators.filter(parts(X, c)) do i
        Y[α(c,i), f] != α(d,X[i, f])
      end))
  end
  Dict(ps)
end

naturality_failures(α::CSetTransformation) =
  naturality_failures(dom(α), codom(α), α.components; combinatorial=true)
naturality_failures(α::TightACSetTransformation) =
  naturality_failures(dom(α), codom(α), α.components)

""" Pretty-print failures of transformation to be natural.

See also: [`naturality_failures`](@ref).
"""
function show_naturality_failures(io::IO, d::AbstractDict)
  println(io, """
    Failures of naturality: a tuple (x,y,y′) on line labelled by f:c→d below
    means that, if the given transformation is α: X → Y, f's naturality square
    fails to commute at x ∈ X(c), with Y(f)(α_c(x))=y and α_d(X(f)(x))=y′.
    """)
  for (f, failures) in pairs(d)
    isempty(failures) && continue
    print(io, "$f: ")
    join(io, failures, ", ")
    println(io)
  end
end

show_naturality_failures(io::IO, α::ACSetMorphism) =
  show_naturality_failures(io, naturality_failures(α))
show_naturality_failures(α::ACSetMorphism) =
  show_naturality_failures(stdout, α)

function is_monic(α::TightACSetTransformation)
  for c in components(α)
    if !is_monic(c) return false end
  end
  return true
end

function is_epic(α::TightACSetTransformation)
  for c in components(α)
    if !is_epic(c) return false end
  end
  return true
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

# Limits and colimits
#####################

⊕(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊕, xs; init=apex(initial(T)))
⊗(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊗, xs; init=apex(terminal(T)))

""" Limit of attributed C-sets that stores the pointwise limits in Set.
"""
@struct_hash_equal struct ACSetLimit{Ob <: ACSet, Diagram,
    Cone <: Multispan{Ob}, Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

""" Colimit of attributed C-sets that stores the pointwise colimits in Set.
"""
@struct_hash_equal struct ACSetColimit{Ob <: ACSet, Diagram,
    Cocone <: Multicospan{Ob}, Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

# By default, products of acsets are taken w.r.t. loose acset morphisms, whereas
# coproducts of acsets are taken w.r.t. tight acset morphisms. We do not need to
# provide defaults for limits and colimits of non-discrete diagrams, because the
# type of the diagram's morphisms disambiguates the situation.

kw_type(; loose::Bool=false, cset::Bool=false) = 
  if loose
    !cset || error("Cannot ask for a Loose CSetTransformation")
    LooseACSetTransformation
  elseif cset 
    CSetTransformation
  else 
    TightACSetTransformation
  end

Limits.terminal(::Type{T}; loose=false, cset=false, kw...) where T <: ACSet =
  limit(EmptyDiagram{T}(kw_type(;loose, cset)); kw...)
Limits.product(X::ACSet, Y::ACSet; loose=false, cset=false,kw...) =
  limit(ObjectPair(X, Y, kw_type(;loose, cset)); kw...)
Limits.product(Xs::AbstractVector{<:ACSet}; loose=false, cset=false, kw...) =
  limit(DiscreteDiagram(Xs, kw_type(;loose, cset)); kw...)

Limits.initial(::Type{T}; kw...) where T <: ACSet =
  colimit(EmptyDiagram{T}(TightACSetTransformation); kw...)
Limits.coproduct(X::ACSet, Y::ACSet; kw...) =
  colimit(ObjectPair(X, Y, TightACSetTransformation); kw...)
Limits.coproduct(Xs::AbstractVector{<:ACSet}; kw...) =
  colimit(DiscreteDiagram(Xs, TightACSetTransformation); kw...)

# Compute limits and colimits in C-Set by reducing to those in Set using the
# "pointwise" formula for (co)limits in functor categories.

function limit(::Type{<:Tuple{ACS,<:TightACSetTransformation}}, diagram) where
    {S, ACS <: StructACSet{S}}
  isempty(attrtypes(S)) || error("Cannot take limit of ACSets with ACSetTransformations")
  limits = map(limit, unpack_diagram(diagram; S=S))
  Xs = cone_objects(diagram)
  pack_limit(ACS, diagram, Xs, limits)
end

"""
Variables are used for the attributes in the apex of limit of CSetTransformations
when there happen to be attributes. However, a commutative monoid on the 
attribute type may be provided in order to avoid introducing variables.
"""
function limit(::Type{<:Tuple{ACS,CSetTransformation}}, diagram; attrfun=(;)) where
  {S, ACS <: StructACSet{S}}
  limits = map(limit, unpack_diagram(diagram; S=S))
  Xs = cone_objects(diagram)
  pack_limit(ACS, diagram, Xs, limits; abstract_product=true, attrfun)
end


"""
A limit of a diagram of ACSets with LooseACSetTransformations.

For general diagram shapes, the apex of the categorical limit will not have
clean Julia types for its attributes, i.e. predicates will be needed to further 
constrain them. `product_attrs` must be turned on in order to avoid an error in 
cases where predicates would be needed. 

`product_attrs=true` will take a limit of the purely combinatorial data, and 
the attribute data of the apex is dictated purely by the ACSets that are have 
explicit cone legs: the value of an attribute (e.g. `f`) for the i'th part in  
the apex is the product `(f(π₁(i)), ..., f(πₙ(i)))` where π maps come from 
the combinatorial part of the limit legs. The type components of the j'th leg of 
the limit is just the j'th cartesian projection.
"""
function limit(::Type{Tuple{ACS,Hom}}, diagram; product_attrs::Bool=false) where
    {S, Ts, ACS <: StructACSet{S,Ts}, Hom <: LooseACSetTransformation}
  limits = map(limit, unpack_diagram(diagram, S=S, all=!product_attrs))
  Xs = cone_objects(diagram)

  attr_lims = (product_attrs ?
    map(limit, unpack_diagram(DiscreteDiagram(Xs, Hom), S=S,Ts=Ts,all=true)) : limits )

  LimitACS = if isempty(attrtypes(S)); ACS
  else
    ACSUnionAll = Base.typename(ACS).wrapper
    ACSUnionAll{(eltype(ob(attr_lims[d])) for d in attrtypes(S))...}
  end

  type_components = [
    Dict(d=>legs(attr_lims[d])[i] for d in attrtypes(S)) for i in eachindex(Xs)]

  limits = NamedTuple(k=>v for (k,v) in pairs(limits) if k ∈ objects(S))
  lim = pack_limit(LimitACS, diagram, Xs, limits;
                   type_components=type_components)
  Y = ob(lim)
  for (f, c, d) in attrs(S)
    Yfs = map((π, X) -> π ⋅ FinDomFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(attr_lims[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  lim
end

""" Make limit of acsets from limits of underlying sets, ignoring attributes.

If one wants to consider the attributes of the apex, the following 
`type_components` - TBD
`abstract_product` - places attribute variables in the apex
`attrfun` - allows one to, instead of placing an attribute in the apex, apply 
            a function to the values of the projections. Can be applied to an
            AttrType or an Attr (which takes precedence).
"""
function pack_limit(::Type{ACS}, diagram, Xs, limits; abstract_product=false, 
                    attrfun=(;), type_components=nothing
                   ) where {S, ACS <: StructACSet{S}}
  Y = ACS()
  for c in objects(S)
    add_parts!(Y, c, length(ob(limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map((π, X) -> π ⋅ FinFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  if abstract_product 
    # Create attrvars for each distinct combination of projection values
    for c in objects(S)
      seen = Dict()
      for part in parts(Y, c)
        for (f, _, d) in attrs(S; from=c)
          monoid = haskey(attrfun, f) ? attrfun[f] : get(attrfun, d, nothing)
          vals = [X[l(part),f] for (l,X) in zip(legs(limits[c]),cone_objects(diagram))]
          if isnothing(monoid)
            if !haskey(seen, vals)
              seen[vals] = add_part!(Y,d)
            end
            set_subpart!(Y, part, f, AttrVar(seen[vals]))
          else 
            set_subpart!(Y, part, f, monoid(vals))
          end
        end
      end
    end
    # Handle attribute components
    alim = NamedTuple(Dict(map(attrtypes(S)) do at 
      T = attrtype_type(Y, at)
      apx = VarSet{T}(nparts(Y, at))
      at => begin 
        vfs = VarFunction{T}[]
        for (i,X) in enumerate(cone_objects(diagram))
          v = map(parts(Y,at)) do p 
            f, c, j = var_reference(Y, at, p)
            X[legs(limits[c])[i](j), f]
          end
          push!(vfs,VarFunction{T}(v, FinSet(nparts(X, at))))
        end
        Multispan(apx,vfs)
      end
    end))
  else
    alim = NamedTuple()
  end 
  πs = pack_components(map(legs, merge(limits,alim)), map(X -> Y, Xs), Xs; 
                       type_components=type_components)
  ACSetLimit(diagram, Multispan(Y, πs), limits)
end

function universal(lim::ACSetLimit, cone::Multispan)
  X = apex(cone)
  S, Ts = acset_schema(X), datatypes(X)
  components = map(universal, lim.limits, unpack_diagram(cone; S=S, Ts=Ts))
  acomps = Dict(map(filter(a->nparts(X,a)>0,attrtypes(S))) do at 
    at => map(parts(X,at)) do p 
      f, c, i = var_reference(X, at, p)
      ob(lim)[components[c](i), f]
    end
  end)
  ACSetTransformation(merge(components,acomps), apex(cone), ob(lim))
end

function colimit(::Type{<:Tuple{ACS,TightACSetTransformation}}, diagram) where {S,Ts,ACS <: StructACSet{S,Ts}}  
  colimits = map(colimit, unpack_diagram(diagram; S=S,Ts=Ts,var=true))
  Xs = cocone_objects(diagram)
  colimit_attrs!(pack_colimit(ACS, S, diagram, Xs, colimits), S, Ts, Xs)
end

function colimit(::Type{<:Tuple{DynamicACSet,TightACSetTransformation}}, diagram) 
  Xs = cocone_objects(diagram)
  X = first(Xs)
  S, Ts, ACS = acset_schema(X), datatypes(X), constructor(X)
  colimits = map(colimit, unpack_diagram(diagram; S=S, Ts=Ts, var=true))
  colimit_attrs!(pack_colimit(ACS, S, diagram, Xs, colimits), S, Ts, Xs)
end

colimit(::Type{<:Tuple{VarSet,<:Any}}, diagram) = 
  colimit(diagram, ToBipartiteColimit())

function colimit(::Type{<:Tuple{ACS,LooseACSetTransformation}}, diagram;
                 type_components=nothing) where {S,Ts, ACS<:StructACSet{S,Ts}}
  isnothing(type_components) &&
    error("Colimits of loose acset transformations are not supported " *
          "unless attrtype components of coprojections are given explicitly")

  ACSUnionAll = Base.typename(ACS).wrapper
  ColimitACS = ACSUnionAll{
    (mapreduce(tc -> eltype(codom(tc[d])), typejoin, type_components)
     for d in attrtypes(S))...}

  colimits = map(colimit, unpack_diagram(diagram; S=S, Ts=Ts))
  Xs = cocone_objects(diagram)
  colimit_attrs!(pack_colimit(ColimitACS, S, diagram, Xs, colimits; 
                              type_components=type_components), S,Ts,Xs)
end

""" Make colimit of acsets from colimits of sets, ignoring attributes.
"""
function pack_colimit(ACS,S, diagram, Xs, colimits; kw...)
  Y = ACS()
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in homs(S)
    Yfs = map((ι, X) -> FinFunction(X, f) ⋅ ι, legs(colimits[d]), Xs)
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs); kw...)
  ACSetColimit(diagram, Multicospan(Y, ιs), colimits)
end


""" Set data attributes of colimit of acsets using universal property.
"""
function colimit_attrs!(colim,S,Ts, Xs) 
  Y, ιs = ob(colim), legs(colim)
  for (attr, c, d) in attrs(S)
    T = attrtype_instantiation(S, Ts, d)
    data = Vector{Union{Some{Union{T,AttrVar}},Nothing}}(nothing, nparts(Y, c))
    for (ι, X) in zip(ιs, Xs)
      ιc, ιd = ι[c], ι[d]
      for i in parts(X, c)
        j = ιc(i)
        if isnothing(data[j])
          data[j] = Some(ιd(subpart(X, i, attr)))
        else
          val1, val2 = ιd(subpart(X, i, attr)), something(data[j])
          val1 == val2 || error(
            "ACSet colimit does not exist: $attr attributes $val1 != $val2")
        end
      end
    end
    set_subpart!(Y, attr, map(something, data))
  end
  colim
end

function universal(colim::ACSetColimit, cocone::Multicospan)
  X = apex(cocone)
  S, Ts = acset_schema(X), datatypes(X)
  ud = unpack_diagram(cocone; S=S, Ts=Ts, var=true)
  components = Dict(k=>collect(universal(colim.colimits[k], ud[k])) for k in keys(ud))
  ACSetTransformation(ob(colim), apex(cocone); components...)
end

""" Diagram in C-Set → named tuple of diagrams in Set.
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet}; kw...) =
  map(DiscreteDiagram, unpack_sets(ob(discrete); kw...))
unpack_diagram(span::Multispan{<:ACSet}; kw...) =
  map(Multispan, sets(apex(span); kw...),
      unpack_components(legs(span); kw...))
unpack_diagram(cospan::Multicospan{<:ACSet}; kw...) =
  map(Multicospan, sets(apex(cospan); kw...),
      unpack_components(legs(cospan); kw...))
unpack_diagram(para::ParallelMorphisms{<:ACSet}; kw...) =
  map(ParallelMorphisms, unpack_components(hom(para); kw...))
unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
  map(ComposableMorphisms, unpack_components(hom(comp); kw...))

function unpack_diagram(diag::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}};
                        S=nothing, Ts=nothing,all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(diag, Ob=X->SetOb(X,c), Hom=α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(diag, Ob=X->VarSet(X,c), Hom=α->α[c]) for c in attrtypes(S)))
  end
  return res 
end
function unpack_diagram(F::Functor{<:FinCat,<:TypeCat{ACS}};
                        S=nothing, Ts=nothing, all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(F, X->SetOb(X,c), α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(F, X->VarSet(X,c), α->α[c]) for c in attrtypes(S)))
  end 
  return res 
end

""" Vector of C-sets → named tuple of vectors of sets.
"""
function unpack_sets(Xs::AbstractVector{<:ACSet}; S=nothing, Ts=nothing,
                     all::Bool=false, var::Bool=false)
  # XXX: The explicit use of `FinSet` and `TypeSet` is needed here for the
  # nullary case (empty vector) because the Julia compiler cannot infer the
  # return type of the more general `SetOb`.
  fin_sets = NamedTuple(c => map(X->FinSet(X,c), Xs) for c in objects(S))
  if all
    return merge(fin_sets, (d => Vector{TypeSet}(map(X->TypeSet(X,d), Xs)) for d in attrtypes(S)))
  elseif var 
    return merge(fin_sets, map(attrtypes(S)) do d 
      T = VarSet{attrtype_instantiation(S,Ts,d)}
      d => T[T(nparts(X,d)) for X in Xs]
    end)
  else 
    return fin_sets
  end 
end

""" Vector of C-set transformations → named tuple of vectors of functions.
"""
function unpack_components(αs::AbstractVector{<:ACSetMorphism};
    S=nothing, Ts=nothing, all::Bool=false, var::Bool=false)
  res = NamedTuple(c => map(α -> α[c], αs) for c in objects(S))
  if !(all || var) return res end 
  f = var ? identity : type_components
  merge(res, NamedTuple(map(attrtypes(S)) do c 
  c => map(α-> f(α)[c] isa LooseVarFunction ? f(α)[c].loose : f(α)[c], αs)
  end))
end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(fs::NamedTuple{names}, doms, codoms;
                         type_components=nothing) where names
  # XXX: Is there a better way?
  components = map((x...) -> NamedTuple{names}(x), fs...)
  if isnothing(type_components) || all(isempty,type_components)
    map(ACSetTransformation, components, doms, codoms)
  else 
    map(LooseACSetTransformation, components, type_components, doms, codoms)
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

# Sub-C-sets
############

""" Sub-C-set of a C-set.
"""
const SubCSet{S} = Subobject{<:StructCSet{S}}
const SubACSet{S} = Subobject{<:StructACSet{S}}

# Componentwise subobjects: coerce VarFunctions to FinFunctions
components(A::SubACSet{S}) where S = 
  NamedTuple(k => Subobject(k ∈ ob(S) ? vs : FinFunction(vs)) 
            for (k,vs) in  pairs(components(hom(A))))

force(A::SubACSet) = Subobject(force(hom(A)))

""" Sub-C-set represented componentwise as a collection of subsets.
"""
@struct_hash_equal struct SubACSetComponentwise{
    Ob<:ACSet, Comp<:NamedTuple} <: Subobject{Ob}
  ob::Ob
  components::Comp

  function SubACSetComponentwise(X::Ob, components::NamedTuple) where Ob<:ACSet
    S = acset_schema(X)
    X_sets = NamedTuple(c => FinSet(X,c) for c in types(S))
    @assert keys(components) ⊆ keys(X_sets)
    coerced_components = NamedTuple{keys(X_sets)}(
      coerce_subob_component(set, get(components, ob, 1:0))
      for (ob, set) in pairs(X_sets))
    new{Ob,typeof(coerced_components)}(X, coerced_components)
  end
end

Subobject(X::ACSet, components::NamedTuple) =
  SubACSetComponentwise(X, components)
Subobject(X::ACSet; components...) = Subobject(X, (; components...))

function coerce_subob_component(X::FinSet, subset::SubFinSet)
  X == ob(subset) ? subset :
    error("Set $X in C-set does not match set of subset $subset")
end
function coerce_subob_component(X::FinSet, f::FinFunction)
  X == codom(f) ? Subobject(f) :
    error("Set $X in C-set does not match codomain of inclusion $f")
end

coerce_subob_component(X::FinSet, f) = Subobject(X, f)

ob(A::SubACSetComponentwise) = A.ob
components(A::SubACSetComponentwise) = A.components

function hom(A::SubACSetComponentwise{T}) where T <: ACSet
  X = ob(A)
  U = constructor(X)()
  hom_components = map(collect∘hom, components(A))
  copy_parts!(U, X, hom_components)
  ACSetTransformation(U, X; Dict(map(collect(pairs(hom_components))) do (k,vs)
    k => k ∈ ob(acset_schema(X)) ? vs : AttrVar.(vs)
  end)...)
end

@instance ThSubobjectBiHeytingAlgebra{ACSet,SubACSet} begin
  @import ob
  meet(A::SubACSet, B::SubACSet) = meet(A, B, SubOpBoolean())
  join(A::SubACSet, B::SubACSet) = join(A, B, SubOpBoolean())
  top(X::ACSet) = top(X, SubOpWithLimits())
  bottom(X::ACSet) = bottom(X, SubOpWithLimits())

  implies(A::SubACSet, B::SubACSet) = implies(A, B, SubOpBoolean())
  subtract(A::SubACSet, B::SubACSet) = subtract(A, B, SubOpBoolean())
  negate(A::SubACSet) = implies(A, bottom(ob(A)), SubOpBoolean())
  non(A::SubACSet) = subtract(top(ob(A)), A, SubOpBoolean())
end

function meet(A::SubACSet, B::SubACSet, ::SubOpBoolean)
  Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
    meet(A₀, B₀, SubOpBoolean())
  end)
end
function join(A::SubACSet, B::SubACSet, ::SubOpBoolean)
  Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
    join(A₀, B₀, SubOpBoolean())
  end)
end
top(X::ACSet, ::SubOpBoolean) =
  Subobject(X, map(X₀ -> top(X₀, SubOpBoolean()), sets(X)))
bottom(X::ACSet, ::SubOpBoolean) =
  Subobject(X, map(X₀ -> bottom(X₀, SubOpBoolean()), sets(X)))

""" Implication of sub-C-sets.

By (Reyes et al 2004, Proposition 9.1.5), the implication ``A ⟹ B`` for two
sub-``C``-sets ``A,B ↪ X`` is given by

``x ∈ (A ⟹ B)(c) iff ∀f: c → c′, x⋅f ∈ A(c′) ⟹ x⋅f ∈ B(c′)``

for all ``c ∈ C`` and ``x ∈ X(c)``. By the definition of implication and De
Morgan's law in classical logic, this is equivalent to

``x ∉ (A ⟹ B)(c) iff ∃f: c → c′, x⋅f ∈ A(c′) ∧ x⋅f ∉ B(c′)``.

In this form, we can clearly see the duality to formula and algorithm for
subtraction of sub-C-sets ([`subtract`](@ref)).
"""
function implies(A::SubACSet{S}, B::SubACSet{S}, ::SubOpBoolean) where S
  X = common_ob(A, B)
  A, B = map(predicate, components(A)), map(predicate, components(B))
  D = NamedTuple([o => trues(nparts(X, o)) for o in types(S)])
  function unset!(c, x)
    D[c][x] = false
    for (c′,x′) in all_incident(X, Val{c}, x)
      if D[c′][x′]; unset!(c′,x′) end
    end
  end

  for c in types(S), x in parts(X,c)
    if D[c][x] && A[c][x] && !B[c][x]; unset!(c,x) end
  end
  Subobject(X, D)
end

""" Subtraction of sub-C-sets.

By (Reyes et al 2004, Sec 9.1, pp. 144), the subtraction ``A ∖ B`` for two
sub-``C``-sets ``A,B ↪ X`` is given by

``x ∈ (A ∖ B)(c) iff ∃f: c′ → c, ∃x′ ∈ f⁻¹⋅x, x′ ∈ A(c′) ∧ x′ ∉ B(c′)``

for all ``c ∈ C`` and ``x ∈ X(c)``. Compare with [`implies`](@ref).
"""
function subtract(A::SubACSet{S}, B::SubACSet{S}, ::SubOpBoolean) where S
  X = common_ob(A, B)
  A, B = map(predicate, components(A)), map(predicate, components(B))
  D = NamedTuple(o => falses(nparts(X, o)) for o in types(S))

  set!(c::Symbol, x::AttrVar) = D[c][x.val] = true
  function set!(c::Symbol, x::Int)
    D[c][x] = true
    for (c′,x′) in all_subparts(X, Val{c}, x)
      if (c′ ∈ ob(S) && !D[c′][x′]) || x′ isa AttrVar 
        set!(c′,x′) 
      end
    end
  end

  for c in types(S), x in parts(X,c)
    if !D[c][x] && A[c][x] && !B[c][x]; set!(c,x) end
  end
  Subobject(X, D)
end

function common_ob(A::Subobject, B::Subobject)
  (X = ob(A)) == ob(B) ||
    error("Subobjects have different base objects: $(ob(A)) != $(ob(B))")
  return X
end

# FIXME: Should these two accessors go elsewhere?

@generated function all_subparts(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:tuple, map(arrows(S; from=c)) do (f,_,c′)
    :($(quot(c′)), subpart(X,x,$(quot(f))))
  end...)
end

@generated function all_incident(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:call, GlobalRef(Iterators, :flatten),
    Expr(:tuple, map(homs(S; to=c)) do (f,c′,_)
      :(Tuple{Symbol,Int}[ ($(quot(c′)),x′) for x′ in incident(X,x,$(quot(f))) ])
    end...))
end


"""A map f (from A to B) as a map of subobjects of A to subjects of B"""
(f::ACSetTransformation)(X::SubACSet) = begin
  ob(X) == dom(f) || error("Cannot apply $f to $X")
  Subobject(codom(f); Dict(map(ob(acset_schema(dom(f)))) do o
    o => sort(unique(f[o].(collect(components(X)[o]))))
  end)...)
end


"""
A map f (from A to B) as a map from A to a subobject of B
# i.e. get the image of f as a subobject of B
"""
(f::ACSetTransformation)(X::StructACSet) =
  X == dom(f) ? f(top(X)) : error("Cannot apply $f to $X")

"""    preimage(f::ACSetTransformation,Y::Subobject)
Inverse of f (from A to B) as a map of subobjects of B to subjects of A.
"""
function preimage(f::ACSetTransformation,Y::SubACSet)
  ob(Y) == codom(f) || error("Cannot apply $f to $X")
  Subobject(dom(f); Dict{Symbol, Vector{Int}}(map(ob(acset_schema(dom(f)))) do o
    o => sort(unique(vcat([preimage(f[o],y) for y in collect(components(Y)[o])]...)))
  end)...)
end

"""    preimage(f::ACSetTransformation,Y::StructACSet)
Inverse f (from A to B) as a map from subobjects of B to subobjects of A.
Cast an ACSet to subobject, though this has a trivial answer when computing
the preimage (it is necessarily the top subobject of A).
"""
preimage(f::ACSetTransformation,Y::StructACSet) =
  Y == codom(f) ? top(dom(f)) : error("Cannot apply inverse of $f to $Y")

# VarACSets
###########

"""
For any ACSet, X, a canonical map A→X where A has distinct variables for all
attributes valued in attrtypes present in `abstract` (by default: all attrtypes)
"""
function abstract_attributes(X::ACSet, abstract=nothing)
  S = acset_schema(X)
  abstract = isnothing(abstract) ? attrtypes(S) : abstract
  A = copy(X)
  comps = Dict{Any, Any}(map(abstract) do at
    rem_parts!(A, at, parts(A, at))
    comp = Union{AttrVar, attrtype_type(X, at)}[]
    for (f, d, _) in attrs(S; to=at)
      append!(comp, X[f])
      A[f] = AttrVar.(add_parts!(A, at, nparts(A, d)))
    end
    at => comp
  end)
  for o in ob(S) comps[o]=parts(X,o) end
  return ACSetTransformation(A,X; comps...)
end 

abstract_attributes(f::ACSetTransformation) = abstract_attributes(dom(f)) ⋅ f

"""
Find some part + attr that refers to an AttrVar. 
Return `nothing` if none exists (i.e. `i` is a wandering variable).
"""
function var_reference(X::ACSet, at::Symbol, i::Int)
  S = acset_schema(X)
  for (f, c, _) in attrs(S; to=at)
    inc = incident(X, AttrVar(i), f)
    if !isempty(inc)
      return (f, c, first(inc))
    end
  end
end


"""
Given a value for each variable, create a morphism X → X′ which applies the 
substitution. We do this via pushout.

  O --> X    where C has AttrVars for `merge` equivalence classes 
  ↓          and O has only AttrVars (sent to concrete values or eq classes 
  C          in the map to C.

`subs` and `merge` are dictionaries keyed by attrtype names

`subs` values are int-keyed dictionaries indicating binding, e.g. 
`; subs = (Weight = Dict(1 => 3.20, 5 => 2.32), ...)`

`merge` values are vectors of vectors indicating equivalence classes, e.g.
`; merge = (Weight = [[2,3], [4,6]], ...)`
"""
function sub_vars(X::ACSet, subs::AbstractDict=Dict(), merge::AbstractDict=Dict()) 
  S = acset_schema(X)
  O, C = [constructor(X)() for _ in 1:2]
  ox_, oc_ = Dict{Symbol, Any}(), Dict{Symbol,Any}()
  for at in attrtypes(S)
    d = get(subs, at, Dict())
    ox_[at] = AttrVar.(filter(p->p ∈ keys(d) && !(d[p] isa AttrVar), parts(X,at)))
    oc_[at] = Any[d[p.val] for p in ox_[at]]
    add_parts!(O, at, length(oc_[at]))

    for eq in get(merge, at, [])
      isempty(eq) && error("Cannot have empty eq class")
      c = AttrVar(add_part!(C, at))
      for var in eq
        add_part!(O, at)
        push!(ox_[at], AttrVar(var))
        push!(oc_[at], c)
      end
    end
  end
  ox = ACSetTransformation(O,X; ox_...)
  oc = ACSetTransformation(O,C; oc_...)
  return first(legs(pushout(ox, oc)))
end 

# Mark as deleted
#################

"""
Check whether an ACSetTransformation is still valid, despite possible deletion 
of elements in the codomain. An ACSetTransformation that isn't in bounds will 
throw an error, rather than return `false`, if run through `is_natural`.
"""
function in_bounds(f::ACSetTransformation) 
  X, Y = dom(f), codom(f)
  S = acset_schema(X)
  all(ob(S)) do o 
    all(parts(X, o)) do i 
      f[o](i) ∈ parts(Y, o)
    end
  end || return false
  all(attrtypes(S)) do o 
    all(AttrVar.(parts(X, o))) do i 
      j = f[o](i) 
      !(j isa AttrVar) || j.val ∈ parts(Y, o)
    end
  end
end

#####################Cartesian morphisms of acsets
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
is_cartesian(f,hs=homs(acset_schema(dom(f)),just_names=true)) = all(h->is_cartesian_at(f,h),hs)


end # module

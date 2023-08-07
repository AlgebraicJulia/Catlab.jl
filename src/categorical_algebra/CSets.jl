""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetTransformation, CSetTransformation, StructACSetTransformation,
  StructTightACSetTransformation, TightACSetTransformation,
  LooseACSetTransformation, SubACSet, SubCSet,
  ACSetHomomorphismAlgorithm, BacktrackingSearch, HomomorphismQuery,
  components, type_components, force,
  naturality_failures, show_naturality_failures, is_natural,
  homomorphism, homomorphisms, is_homomorphic,
  isomorphism, isomorphisms, is_isomorphic,
  @acset_transformation, @acset_transformations,
  subobject_graph, partial_overlaps, maximum_common_subobject,
  abstract_attributes

using Base.Iterators: flatten
using Base.Meta: quot
using DataStructures: BinaryHeap, DefaultDict
using MLStyle: @match
using Random
using Reexport
using StructEquality

using CompTime
@reexport using ACSets
@reexport using ...ACSetsGATsInterop
using ACSets.Columns
using ACSets.DenseACSets: indices, unique_indices, attr_type, attrtype_type,
  datatypes, constructor, delete_subobj!

using ...GATs, ...Graphs.BasicGraphs
using ...Theories: ThCategory, Hom, Ob, Attr, AttrType
import ...Theories: ob, hom, dom, codom, compose, ⋅, id,
  meet, ∧, join, ∨, top, ⊤, bottom, ⊥
using ..FreeDiagrams, ..Limits, ..Subobjects, ..Sets, ..FinSets, ..FinCats
using ..FinSets: VarFunction, LooseVarFunction, IdentityFunction, VarSet
import ..Limits: limit, colimit, universal
import ..Subobjects: Subobject, implies, ⟹, subtract, \, negate, ¬, non, ~
import ..Sets: SetOb, SetFunction, TypeSet
using ..Sets
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
  if type ∈ ob(S)
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
    VarFunction(FinFunction(X,f))
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
  # FIXME: The equations should not be here. They should be in the acset, which
  # is not yet supported for struct acsets.
  equations::Vector{Pair}
end
FinDomFunctor(X::ACSet; equations=Pair[]) = ACSetFunctor(X, equations)
ACSet(X::ACSetFunctor) = X.acset

hasvar(X::ACSet) = any(o->nparts(X,o) > 0, attrtypes(acset_schema(X)))
hasvar(X::ACSetFunctor) = hasvar(X.acset)

function dom(F::ACSetFunctor)
  pres = Presentation(F.acset)
  add_equations!(pres, F.equations)
  FinCat(pres)
end

function codom(F::ACSetFunctor)
  hasvar(F) ? TypeCat{VarSet,VarFunction}() :
    TypeCat{SetOb,FinDomFunction{Int}}()
end

Categories.do_ob_map(F::ACSetFunctor, x) = 
  (hasvar(F) ? VarSet : SetOb)(F.acset, functor_key(x))
Categories.do_hom_map(F::ACSetFunctor, f) =  
  (hasvar(F) ? VarFunction : FinFunction)(F.acset, functor_key(f))

functor_key(x) = x
functor_key(expr::GATExpr{:generator}) = first(expr)

# Set-valued FinDomFunctors as ACSets.
(T::Type{ACS})(F::Diagram) where ACS <: ACSet = F |> diagram |> T
function (::Type{ACS})(F::FinDomFunctor) where ACS <: ACSet
  X = if ACS isa UnionAll
    pres = presentation(dom(F))
    ACS{(eltype(ob_map(F, c)) for c in generators(pres, :AttrType))...}()
  else
    ACS()
  end
  copy_parts!(X, F)
  return X
end

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
    dom_parts = added[nameof(dom(f))]
    set_subpart!(X, dom_parts, nameof(f), collect(hom_map(F, f)))
  end
  added
end

# C-set transformations
#######################

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
abstract type ACSetTransformation{Dom,Codom} end

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

components(α::ACSetTransformation) = α.components
force(α::ACSetTransformation) = map_components(force, α)

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
"""
const CSetTransformation{Dom<:StructCSet,Codom<:StructCSet} =
  TightACSetTransformation{Dom,Codom}

CSetTransformation(components, X::StructCSet{S}, Y::StructCSet{S}) where S =
  StructTightACSetTransformation{S}(components, X, Y)
CSetTransformation(X::StructCSet{S}, Y::StructCSet{S}; components...) where S =
  StructTightACSetTransformation{S}((; components...), X, Y)

TightACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where S =
  StructTightACSetTransformation{S}(components, X, Y)

# Component coercion

function coerce_components(S, components, X,Y)
  @assert keys(components) ⊆ objects(S) ∪ attrtypes(S)
  ocomps = NamedTuple(
    c => coerce_component(c, get(components,c,1:0), nparts(X,c), nparts(Y,c))
    for c in objects(S))
  acomps = NamedTuple(map(attrtypes(S)) do c
    c => coerce_attrvar_component(c, get(components,c,1:0), 
          TypeSet(X, c), TypeSet(Y, c), nparts(X,c), nparts(Y,c))
  end)
    return merge(ocomps, acomps)
end 
  
function coerce_component(ob::Symbol, f::FinFunction{Int,Int},
                          dom_size::Int, codom_size::Int)
  length(dom(f)) == dom_size || error("Domain error in component $ob")
  length(codom(f)) == codom_size || error("Codomain error in component $ob")
  return f
end

coerce_component(::Symbol, f, dom_size::Int, codom_size::Int) =
  FinFunction(f, dom_size, codom_size)

function coerce_attrvar_component(
    ob::Symbol, f::AbstractVector,::TypeSet{T}, ::TypeSet{T},
    dom_size::Int, codom_size::Int) where {T}
  e = "Domain error in component $ob variable assignment $(length(f)) != $dom_size"
  length(f) == dom_size || error(e)
  return VarFunction{T}(f, FinSet(codom_size))
end

function coerce_attrvar_component(
    ob::Symbol, f::VarFunction,::TypeSet{T},::TypeSet{T},
    dom_size::Int, codom_size::Int) where {T}
  # length(dom(f.fun)) == dom_size || error("Domain error in component $ob: $(dom(f.fun))!=$dom_size")
  length(f.codom) == codom_size || error("Codomain error in component $ob: $(f.fun.codom)!=$codom_size")
  return f
end

function coerce_attrvar_component(
    ob::Symbol, f::LooseVarFunction,d::TypeSet{T},cd::TypeSet{T′},
    dom_size::Int, codom_size::Int) where {T,T′}
  length(dom(f.fun)) == dom_size || error("Domain error in component $ob")
  length(f.codom) == codom_size || error("Codomain error in component $ob: $(f.fun.codom)!=$codom_size")
  # We do not check types (equality is too strict)
  # dom(f.loose) == d || error("Dom of type comp mismatch $(dom(f.loose)), $d")
  # codom(f.loose) == cd || error("Codom of type comp mismatch $(codom(f.loose)), $cd")
  return f
end

function Base.getindex(α::ACSetTransformation, c) 
  get(α.components, c) do
    c ∈ attrtypes(acset_schema(dom(α))) || error("No object or attribute type with name $c")
    SetFunction(identity, TypeSet(dom(α),c), TypeSet(codom(α),c))
  end
end

map_components(f, α::ACSetTransformation) =
  ACSetTransformation(map(f, components(α)), dom(α), codom(α))

function Base.show(io::IO, α::ACSetTransformation)
  print(io, "ACSetTransformation(")
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
  is_tight = true 
  for a in acomps 
    is_tight &= (a isa Union{VarFunction, Function, AbstractVector} || a.loose isa IdentityFunction)
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
For each hom in the schema, e.g. h: m → n, the following square commute must:

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
  is_natural(dom(α),codom(α),α.components,type_components(α))
end
function is_natural(α::ACSetTransformation)
  is_natural(dom(α),codom(α),α.components)
end
function is_natural(dom,codom,comps...)
  all(isempty,[a.second for a in naturality_failures(dom,codom,comps...)])
end

"""
Returns a dictionary whose keys are contained in the names in `arrows(S)`
and whose value at `:f`, for an arrow `(f,c,d)`, is a lazy iterator
over the elements of X(c) on which α's naturality square
for f does not commute. Components should be a NamedTuple or Dictionary
with keys contained in the names of S's morphisms and values vectors or dicts
defining partial functions from X(c) to Y(c).
"""
function naturality_failures(X,Y,comps)
  S = acset_schema(X)
  type_comps = Dict(attr=>SetFunction(identity,SetOb(X,attr),SetOb(X,attr)) for attr in attrtype(S))
  naturality_failures(X,Y,comps,type_comps)
end
function naturality_failures(X,Y,comps,type_comps)
  S = acset_schema(X)
  comps = Dict(a=> isa(comps[a],Union{SetFunction,VarFunction,LooseVarFunction}) ? comps[a] : FinDomFunction(comps[a])  for a in keys(comps))
  type_comps = Dict(a=>isa(type_comps[a],Union{SetFunction,VarFunction,LooseVarFunction}) ? type_comps[a] : 
                        SetFunction(type_comps[a],TypeSet(X,a),TypeSet(Y,a)) for a in keys(type_comps))
  α = merge(comps,type_comps)
  arrs = [(f,c,d) for (f,c,d) in arrows(S) if haskey(α,c) && haskey(α,d)]
  ps = Iterators.map(arrs) do (f,c,d)
    Xf,Yf,α_c,α_d = subpart(X,f),subpart(Y,f), α[c], α[d]
    Pair(f,
    Iterators.map(i->(i,Yf[α_c(i)],α_d(Xf[i])),
      Iterators.filter(dom(α_c)) do i
        Xf[i] in dom(α_d) && Yf[α_c(i)] != α_d(Xf[i])
      end))
  end
  Dict(ps)
end

naturality_failures(α::TightACSetTransformation) =
  naturality_failures(dom(α), codom(α), α.components)
naturality_failures(α::LooseACSetTransformation)=
  naturality_failures(dom(α), codom(α), α.components, α.type_components)

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

show_naturality_failures(io::IO, α::ACSetTransformation) =
  show_naturality_failures(io, naturality_failures(α))
show_naturality_failures(α::ACSetTransformation) =
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

"""
Provides a shorthand for constructing a tight acset transformation by giving its
components. Homomorphism search allows partial specification, with the return
value being the unique extension if it exists.

Keyword arguments can be passed on to the search function after the body of the
transformation.

Example usage for transformation between `WeightedGraph{String}`:

```
@acset_transformation A B begin
  V = [3,5,2] #complete specification can be a vector
  E = Dict(1 => 3, 4 => 3) #otherwise use a dict
end monic=true iso=[:V] or [:V,:E], etc
```
"""
macro acset_transformation(dom,cod,kw...)
  kw = map(parse_kwargs,kw)
  Expr(:call,esc(:homomorphism),esc(dom),esc(cod), Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformation(dom,cod,body,kw...)
  kw = map(parse_kwargs,kw)
  initial = process_initial(body)
  Expr(:call,esc(:homomorphism),esc(dom),esc(cod),initial,Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformations(dom,cod,kw...)
  kw = map(parse_kwargs,kw)
  Expr(:call,esc(:homomorphisms),esc(dom),esc(cod),Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformations(dom,cod,body,kw...)
  kw = map(parse_kwargs,kw)
  initial = process_initial(body)
  Expr(:call,esc(:homomorphisms),esc(dom),esc(cod),initial,Expr(:kw,:error_failures,true),kw...)
end
function process_initial(expr)
  initial = @match expr begin
    Expr(:block,lines...) => filter(!isnothing,map(escape_assignment_lhs,lines))
    Expr(:(=),x,y) => parse_kwargs(expr) #does this ever happen?
    _ => error("Expected begin...end block or kwarg, received $expr")
  end
  isa(initial,Vector) ? length(initial) > 0 ?
      Expr(:kw,:initial,Expr(:tuple,initial...)) :
      Expr(:kw,:initial,Expr(:tuple,Expr(:parameters,))) :
    initial
end
function parse_kwargs(expr)
  @match expr begin
    Expr(:(=),x,y) => Expr(:kw,x,y)
    _ => nothing
  end
end
function escape_assignment_lhs(expr)
  @match expr begin
    Expr(:(=),x,y) => Expr(:(=),esc(x),y)
    _ => nothing
  end
end

# Category of C-sets
####################

@instance ThCategory{ACSet, ACSetTransformation} begin
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

# Finding C-set transformations
###############################

""" Algorithm for finding homomorphisms between attributed ``C``-sets."""
abstract type ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using backtracking search.

This procedure uses the classic backtracking search algorithm for a
combinatorial constraint satisfaction problem (CSP). As is well known, the
homomorphism problem for relational databases is reducible to CSP. Since the
C-set homomorphism problem is "the same" as the database homomorphism problem
(insofar as attributed C-sets are "the same" as relational databases), it is
also reducible to CSP. Backtracking search for CSP is described in many computer
science textbooks, such as (Russell & Norvig 2010, *Artificial Intelligence*,
Third Ed., Chapter 6: Constraint satisfaction problems, esp. Algorithm 6.5). In
our implementation, the search tree is ordered using the popular heuristic of
"minimum remaining values" (MRV), also known as "most constrained variable.
"""
struct BacktrackingSearch <: ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using a conjunctive query.

This algorithm evaluates a conjunctive query (limit in `FinSet`) to find all
homomorphisms between two ``C``-sets. In fact, conjunctive queries are exactly
the *representable* functors from ``C``-sets to sets, so every conjunctive query
arises in this way, with the caveat that conjunctive queries may correspond to
to infinite ``C``-sets when ``C`` is infinite (but possibly finitely presented).
"""
struct HomomorphismQuery <: ACSetHomomorphismAlgorithm end

""" Find a homomorphism between two attributed ``C``-sets.

Returns `nothing` if no homomorphism exists. For many categories ``C``, the
``C``-set homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.

To restrict to *monomorphisms*, or homomorphisms whose components are all
injective functions, set the keyword argument `monic=true`. To restrict only
certain components to be injective or bijective, use `monic=[...]` or
`iso=[...]`. For example, setting `monic=[:V]` for a graph homomorphism ensures
that the vertex map is injective but imposes no constraints on the edge map.

To restrict the homomorphism to a given partial assignment, set the keyword
argument `initial`. For example, to fix the first source vertex to the third
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`. Use 
the keyword argument `type_components` to specify nontrivial components on 
attribute types for a loose homomorphism. These components must be callable:
either Julia functions on the appropriate types or FinFunction(Dict(...)).

Use the keyword argument `alg` to set the homomorphism-finding algorithm. By
default, a backtracking search algorithm is used ([`BacktrackingSearch`](@ref)).
Use the keyword argument error_failures = true to get errors explaining 
any immediate inconsistencies in specified initial data.

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
  result = nothing
  backtracking_search(X, Y; kw...) do α
    result = α; return true
  end
  result
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
homomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphisms(X, Y, alg; kw...)

function homomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) 
  results = []
  backtracking_search(X, Y; kw...) do α
    push!(results, map_components(deepcopy, α)); return false
  end
  results
end

""" Is the first attributed ``C``-set homomorphic to the second?

This function generally reduces to [`homomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_homomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_homomorphic(X, Y, alg; kw...)

is_homomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(homomorphism(X, Y, alg; kw...))

""" Find an isomorphism between two attributed ``C``-sets, if one exists.

See [`homomorphism`](@ref) for more information about the algorithms involved.
"""
isomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphism(X, Y, alg; kw...)

isomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphism(X, Y, alg; iso=true, initial=initial)

""" Find all isomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`isomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
isomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphisms(X, Y, alg; kw...)

isomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphisms(X, Y, alg; iso=true, initial=initial)

""" Are the two attributed ``C``-sets isomorphic?

This function generally reduces to [`isomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_isomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_isomorphic(X, Y, alg; kw...)

is_isomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(isomorphism(X, Y, alg; kw...))

# Backtracking search
#--------------------

""" Get assignment pairs from partially specified component of C-set morphism.
"""
partial_assignments(x::FinFunction; is_attr=false) = partial_assignments(collect(x))
partial_assignments(x::AbstractDict; is_attr=false) = pairs(x)
partial_assignments(x::AbstractVector; is_attr=false) =
  ((i,y) for (i,y) in enumerate(x) if is_attr || (!isnothing(y) && y > 0))

# FIXME: Should these accessors go elsewhere?
in_hom(S, c) = [dom(S,f) => f for f in hom(S) if codom(S,f) == c]
out_hom(S, c) = [f => codom(S,f) for f in hom(S) if dom(S,f) == c]


""" Internal state for backtracking search for ACSet homomorphisms.

Assignment of attribute variables maintains both the assignment as well as the 
number of times that variable has been bound. We can only *freely* assign the 
variable to match any AttrVar or concrete attribute value if it has not yet 
been bound.
"""
struct BacktrackingState{
  Dom <: ACSet, Codom <: ACSet,
  Assign <: NamedTuple, PartialAssign <: NamedTuple, LooseFun <: NamedTuple,
  }
  assignment::Assign
  assignment_depth::Assign
  inv_assignment::PartialAssign
  dom::Dom
  codom::Codom
  type_components::LooseFun
end

function backtracking_search(f, X::ACSet, Y::ACSet;
    monic=false, iso=false, random=false, 
    type_components=(;), initial=(;), error_failures=false)
  S, Sy = acset_schema.([X,Y])
  S == Sy || error("Schemas must match for morphism search")
  Ob = Tuple(objects(S))
  Attr = Tuple(attrtypes(S))
  ObAttr = Tuple(objects(S) ∪ attrtypes(S))
  # Fail if there are "free floating attribute variables"
  all(attrtypes(S)) do a_type
    ats = attrs(S, just_names=true, to=a_type)
    avs = collect.([filter(x->x isa AttrVar, X[f]) for f in ats])
    pa = partial_assignments(get(initial, a_type, []); is_attr=true)
    initkeys = AttrVar.(keys(collect(pa)))
    length(unique(vcat(initkeys, avs...))) == nparts(X, a_type) 
  end || error("Cannot search for morphisms with free-floating variables")

  # Fail early if no monic/isos exist on cardinality grounds.
  if iso isa Bool
    iso = iso ? Ob : ()
  end
  if monic isa Bool
    monic = monic ? Ob : ()
  end
  iso_failures = Iterators.filter(c->nparts(X,c)!=nparts(Y,c),iso)
  mono_failures = Iterators.filter(c->nparts(X,c)>nparts(Y,c),monic)  
  if (!isempty(iso_failures) || !isempty(mono_failures))
    if !error_failures 
      return false 
    else error("""
      Cardinalities inconsistent with request for...
        iso at object(s) $iso_failures
        mono at object(s) $mono_failures
      """)
    end
  end

  # Injections between finite sets of the same size are bijections, so reduce to that case.
  monic = unique([iso..., monic...])

  if error_failures 
    uns = naturality_failures(X,Y,initial,type_components)
    all(isempty,[uns[a] for a in keys(uns)]) ||
      error(sprint(show_naturality_failures, uns))
  end

  # Initialize state variables for search.
  assignment = merge(
    NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob),
    NamedTuple{Attr}(Pair{Int,Union{AttrVar,attrtype_type(X,c)}}[
      0 => AttrVar(0) for _ in parts(X,c)] for c in Attr)
  )
  assignment_depth = map(copy, assignment)
  inv_assignment = NamedTuple{ObAttr}(
    (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in ObAttr)
  loosefuns = NamedTuple{Attr}(
    isnothing(type_components) ? identity : get(type_components, c, identity) for c in Attr)
  state = BacktrackingState(assignment, assignment_depth, 
                                  inv_assignment, X, Y, loosefuns)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments; is_attr = c ∈ Attr)
      if c ∈ ob(S)
        assign_elem!(state, 0, c, x, y) || return false
      else 
        # assign_elem! doesn't expect an attrtype part
        state.assignment[c][x][1] == 0 || assignment[c][x][2] == y || return false
        state.assignment[c][x] = 1 => y
      end 
    end
  end
  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1; random=random)
end

function backtracking_search(f, state::BacktrackingState, depth::Int; 
                              random=false) 
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    if any(!=(identity), state.type_components)
      return f(LooseACSetTransformation(
        state.assignment, state.type_components, state.dom, state.codom))
    else
      S = acset_schema(state.dom)
      od = Dict{Symbol,Vector{Int}}(k=>(state.assignment[k]) for k in objects(S))
      ad = Dict(k=>last.(state.assignment[k]) for k in attrtypes(S))
      comps = merge(NamedTuple(od),NamedTuple(ad))
      return f(ACSetTransformation(comps, state.dom, state.codom))
    end
  elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return false
  end
  c, x = mrv_elem

  # Attempt all assignments of the chosen element.
  Y = state.codom
  for y in (random ? shuffle : identity)(parts(Y, c))
    (assign_elem!(state, depth, c, x, y) 
      && backtracking_search(f, state, depth + 1)) && return true
    unassign_elem!(state, depth, c, x)
  end
  return false
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState, depth)
  S = acset_schema(state.dom)
  mrv, mrv_elem = Inf, nothing
  Y = state.codom
  for c in ob(S), (x, y) in enumerate(state.assignment[c])
    y == 0 || continue
    n = count(can_assign_elem(state, depth, c, x, y) for y in parts(Y, c))
    if n < mrv
      mrv, mrv_elem = n, (c, x)
    end
  end
  (mrv, mrv_elem)
end

""" Check whether element (c,x) can be assigned to (c,y) in current assignment.
"""
function can_assign_elem(state::BacktrackingState, depth, c, x, y)
  # Although this method is nonmutating overall, we must temporarily mutate the
  # backtracking state, for several reasons. First, an assignment can be a
  # consistent at each individual subpart but not consistent for all subparts
  # simultaneously (consider trying to assign a self-loop to an edge with
  # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
  # must keep track of which elements we have visited to avoid looping forever.
  ok = assign_elem!(state, depth, c, x, y)
  unassign_elem!(state, depth, c, x)
  return ok
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.

Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""
assign_elem!(state::BacktrackingState{<:StructACSet{S}}, depth, c, x, y) where S = 
  _assign_elem!(Val{S}, state, depth,Val{c},x,y)
assign_elem!(state::BacktrackingState{<:DynamicACSet}, depth, c, x, y) =
  runtime(_assign_elem!,acset_schema(state.dom), state, depth,c,x,y)


@ct_enable function _assign_elem!(@ct(S), state::BacktrackingState, depth, @ct(c), x, y)
  y′ = state.assignment[@ct c][x]
  y′ == y && return true  # If x is already assigned to y, return immediately.
  y′ == 0 || return false # Otherwise, x must be unassigned.
  if !isnothing(state.inv_assignment[@ct c]) && state.inv_assignment[@ct c][y] != 0
    # Also, y must unassigned in the inverse assignment.
    return false
  end

  # Check attributes first to fail as quickly as possible.
  X, Y = state.dom, state.codom
  @ct_ctrl for (f, _, d) in attrs(S; from=c)
    dcomp = state.type_components[@ct(d)]
    if subpart(X,x,@ct(f)) isa AttrVar
      xcount, xval = state.assignment[@ct(d)][subpart(X,x,@ct(f)).val]
      if xcount > 0 && dcomp(xval) != subpart(Y,y,@ct(f)) 
         return false
      end
    elseif dcomp(subpart(X,x,@ct f)) != subpart(Y,y,@ct f)
      return false
    end 

  end

  # Make the assignment and recursively assign subparts.
  state.assignment[@ct c][x] = y
  state.assignment_depth[@ct c][x] = depth
  if !isnothing(state.inv_assignment[@ct c])
    state.inv_assignment[@ct c][y] = x
  end

  @ct_ctrl for (f,_,d) in attrs(S; from=c)
    if subpart(X,x,@ct(f)) isa AttrVar
      v = subpart(X,x,@ct(f)).val
      xcount,_ = state.assignment[@ct d][v]
      state.assignment[@ct d][v] = xcount+1 => subpart(Y,y,@ct(f))
    end
  end

  @ct_ctrl for (f, _, d) in homs(S; from=c) 
    assign_elem!(state, depth, @ct(d), subpart(X,x,@ct f),subpart(Y,y,@ct f)) || return false
  end
  return true
end

""" Unassign the element (c,x) in the current assignment.
"""
unassign_elem!(state::BacktrackingState{<:StructACSet{S}}, depth, c, x) where S = 
  _unassign_elem!(Val{S}, state, depth,Val{c},x)
unassign_elem!(state::BacktrackingState{<:DynamicACSet}, depth, c, x) =
  runtime(_unassign_elem!,acset_schema(state.dom), state, depth,c,x)

@ct_enable function _unassign_elem!(@ct(S), state::BacktrackingState, depth, @ct(c), x) 
  state.assignment[@ct c][x] == 0 && return
  assign_depth = state.assignment_depth[@ct c][x]
  @assert assign_depth <= depth
  if assign_depth == depth
    X = state.dom
    if !isnothing(state.inv_assignment[@ct c])
      y = state.assignment[@ct c][x]
      state.inv_assignment[@ct c][y] = 0
    end

    @ct_ctrl for (f,_,d) in attrs(S; from=c)
      if subpart(X,x,@ct(f)) isa AttrVar
        v = subpart(X,x,@ct(f)).val
        n, αv = state.assignment[@ct(d)][v]
        state.assignment[@ct(d)][v]= (n-1 => αv)
      end
    end

    state.assignment[@ct c][x] = 0
    state.assignment_depth[@ct c][x] = 0
    @ct_ctrl for (f, d) in out_hom(S, c)
      unassign_elem!(state, depth, @ct(d), subpart(X,x,@ct(f)))
    end
  end
end

# Limits and colimits
#####################

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

Limits.terminal(::Type{T}; kw...) where T <: ACSet =
  limit(EmptyDiagram{T}(LooseACSetTransformation); kw...)
Limits.product(X::ACSet, Y::ACSet; kw...) =
  limit(ObjectPair(X, Y, LooseACSetTransformation); kw...)
Limits.product(Xs::AbstractVector{<:ACSet}; kw...) =
  limit(DiscreteDiagram(Xs, LooseACSetTransformation); kw...)

Limits.initial(::Type{T}; kw...) where T <: ACSet =
  colimit(EmptyDiagram{T}(TightACSetTransformation); kw...)
Limits.coproduct(X::ACSet, Y::ACSet; kw...) =
  colimit(ObjectPair(X, Y, TightACSetTransformation); kw...)
Limits.coproduct(Xs::AbstractVector{<:ACSet}; kw...) =
  colimit(DiscreteDiagram(Xs, TightACSetTransformation); kw...)

# Compute limits and colimits in C-Set by reducing to those in Set using the
# "pointwise" formula for (co)limits in functor categories.

function limit(::Type{<:Tuple{ACS,TightACSetTransformation}}, diagram) where
    {S, ACS <: StructCSet{S}}
  limits = map(limit, unpack_diagram(diagram; S=S))
  Xs = cone_objects(diagram)
  pack_limit(ACS, diagram, Xs, limits)
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
  lim = pack_limit(LimitACS, diagram, Xs, limits; type_components = type_components)
  Y = ob(lim)
  for (f, c, d) in attrs(S)
    Yfs = map((π, X) -> π ⋅ FinDomFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(attr_lims[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  lim
end

""" Make limit of acsets from limits of underlying sets, ignoring attributes.
"""
function pack_limit(::Type{ACS}, diagram, Xs, limits; type_components=nothing) where
    {S, ACS <: StructACSet{S}}
  Y = ACS()
  for c in objects(S)
    add_parts!(Y, c, length(ob(limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map((π, X) -> π ⋅ FinFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  πs = pack_components(map(legs, limits), map(X -> Y, Xs), Xs; type_components=type_components)
  ACSetLimit(diagram, Multispan(Y, πs), limits)
end

function universal(lim::ACSetLimit, cone::Multispan)
  X = apex(cone)
  S, Ts = acset_schema(X), datatypes(X)
  components = map(universal, lim.limits, unpack_diagram(cone; S=S, Ts=Ts))
  CSetTransformation(components, apex(cone), ob(lim))
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
function unpack_components(αs::AbstractVector{<:ACSetTransformation};
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

# Cast VarFunctions to FinFunctions
components(A::SubACSet{S}) where S = 
  NamedTuple(k => Subobject(
    k ∈ ob(S) ? vs : FinFunction([v.val for v in collect(vs)], FinSet(codom(vs))))
  for (k,vs) in pairs(components(hom(A)))
)

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

  function set!(c, x)
    D[c][x] = true
    for (c′,x′) in all_subparts(X, Val{c}, x)
      if !D[c′][x′]; set!(c′,x′) end
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
  Expr(:tuple, map(out_hom(S, c)) do (f,c′)
    :($(quot(c′)), subpart(X,x,$(quot(f))))
  end...)
end

@generated function all_incident(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:call, GlobalRef(Iterators, :flatten),
    Expr(:tuple, map(in_hom(S, c)) do (c′,f)
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

"""    preimage(f::CSetTransformation,Y::StructACSet)
Inverse f (from A to B) as a map from subobjects of B to subobjects of A.
Cast an ACSet to subobject, though this has a trivial answer when computing
the preimage (it is necessarily the top subobject of A).
"""
preimage(f::CSetTransformation,Y::StructACSet) =
  Y == codom(f) ? top(dom(f)) : error("Cannot apply inverse of $f to $Y")

# VarACSets
###########

"""
For any ACSet, X, a canonical map A→X where A has distinct variables for all
subparts.
"""
function abstract_attributes(X::ACSet)
  S = acset_schema(X)
  A = copy(X)
  comps = Dict{Any, Any}(map(attrtypes(S)) do at
    rem_parts!(A, at, parts(A, at))
    comp = Union{AttrVar, attrtype_type(X, at)}[]
    for (f, d, _) in attrs(S; to=at)
      append!(comp, X[f])
      A[f] = AttrVar.(add_parts!(A, at, nparts(A, d)))
    end
    at => comp
  end)
  for o in ob(S)
    comps[o] = parts(X, o)
  end
  ACSetTransformation(A, X; comps...)
end

# Maximum Common C-Set
######################

""" Compute the size of a C-Set

Defintion: let 𝐺: C → 𝐒et be a C-set, we define the _size_ of 𝐺 to be ∑_{c ∈ C}
|𝐺c|.  For example, under this definition, the size of:
  * a graph G is |GE| + |GV| (num edges + num vertices)
  * a Petri net P is |PT| + |PS| + |PI| + |PO| (num transitions + num species +
    num input arcs + num output arcs).
"""
total_parts(X::ACSet) = mapreduce(oₛ -> nparts(X, oₛ), +, objects(acset_schema(X)); init=0)
total_parts(X::ACSetTransformation) = total_parts(dom(X)) 

"""
Enumerate subobjects of an ACSet in order of largest to smallest 
(assumes no wandering variables).
"""
struct SubobjectIterator
  top::ACSet
end

Base.eltype(::Type{SubobjectIterator}) = Subobject
Base.IteratorSize(::Type{SubobjectIterator}) = Base.SizeUnknown()

"""
Preorder of subobjects via inclusion. 
Returns a graph + list of subobjects corresponding to its vertices. 
The subobjects are ordered by decreasing size (so it's topologically sorted)
"""
function subobject_graph(X::ACSet)
  S = acset_schema(X)
  subs = X |> SubobjectIterator |> collect
  G = Graph(length(subs))
  for (i,s1) in enumerate(subs)
    for (j,s2) in enumerate(subs)
      if all(ob(S)) do o 
          collect(hom(s1)[o]) ⊆ collect(hom(s2)[o])
        end
        add_edge!(G, i, j)
      end
    end
  end
  return (G, subs)
end

"""
seen       - any subobject we've seen so far
to_recurse - frontier of subobjects we've yet to recursively explore
to_yield   - Subobjects which we've yet to yield
"""
struct SubobjectIteratorState
  seen::Set{ACSetTransformation}
  to_recurse::BinaryHeap
  to_yield::BinaryHeap
  function SubobjectIteratorState()  
    heap = BinaryHeap(Base.By(total_parts, Base.Order.Reverse), ACSetTransformation[])
    new(Set{ACSetTransformation}(), heap, deepcopy(heap))
  end
end
Base.isempty(S::SubobjectIteratorState) = isempty(S.seen)
function Base.push!(S::SubobjectIteratorState,h::ACSetTransformation)
  push!(S.seen, h); push!(S.to_recurse, h); push!(S.to_yield, h)
end

"""This would be much more efficient with canonical isomorph"""
function is_seen(S::SubobjectIteratorState, f::ACSetTransformation)
  for h in S.seen 
    if any(σ -> force(σ⋅h) == force(f), isomorphisms(dom(f),dom(h)))
      return true 
    end
  end
  return false
end

"""
We recurse only if there is nothing to yield or we have something to recurse on 
that is bigger than the biggest thing in our to-yield set.
"""
should_yield(S::SubobjectIteratorState) = !isempty(S.to_yield) && (
    isempty(S.to_recurse) || total_parts(first(S.to_yield)) > total_parts(first(S.to_recurse)))


function Base.iterate(Sub::SubobjectIterator, state=SubobjectIteratorState())
  S = acset_schema(Sub.top)
  T = id(Sub.top)
  if isempty(state) # first time
    push!(state.seen, T); push!(state.to_recurse, T)
    return (Subobject(T), state)
  end

  # Before recursing, check if we should yield things or terminate
  if should_yield(state)
    return (Subobject(pop!(state.to_yield)), state)
  end
  if isempty(state.to_recurse) 
    return nothing
  end
  # Explore by trying to delete each ACSet part independently 
  X = pop!(state.to_recurse)
  dX = dom(X)
  for o in ob(S)
    for p in parts(dX, o)
      rem = copy(dX)
      comps = delete_subobj!(rem, Dict([o => [p]]))
      h = ACSetTransformation(rem, dX; comps...) ⋅ X
      if !is_seen(state, h)
        push!(state, h)
      end
    end
  end

  if should_yield(state)
    return (Subobject(pop!(state.to_yield)), state)
  elseif !isempty(state.to_recurse)
    return Base.iterate(Sub, (state))
  else 
    return nothing
  end 
end


struct OverlapIterator
  top::ACSet
  others::Vector{ACSet}
  function OverlapIterator(Xs::Vector{T}) where T<:ACSet
    t, o... = sort(Xs, by=total_parts)
    new(t, o)
  end
end
Base.eltype(::Type{OverlapIterator}) = Multispan
Base.IteratorSize(::Type{OverlapIterator}) = Base.SizeUnknown()

mutable struct OverlapIteratorState
  curr_subobj::Union{Nothing,ACSetTransformation}
  subobject_state::Iterators.Stateful{SubobjectIterator}
  seen::Set{Multispan}
  maps::Union{Nothing,Iterators.Stateful{<:Iterators.ProductIterator}}
  OverlapIteratorState(x::ACSet) = 
    new(nothing, Iterators.Stateful(SubobjectIterator(x)), Set{Multispan}(), nothing)
end

# Could be cleaner/faster if we used CSetAutomorphisms to handle symmetries
"""
Given a list of ACSets X₁...Xₙ, find all multispans A ⇉ X ordered by decreasing 
number of total parts of A.

We search for overlaps guided by iterating through the subobjects of the 
smallest ACSet.
  
If a subobject of the first object, A↪X, has multiple maps into X₁, then 
we need to cache a lot of work because we consider each such subobject 
independently. This is the maps from A into all the other objects as well as the 
automorphisms of A.  
"""
function Base.iterate(Sub::OverlapIterator, state=nothing)
  state = isnothing(state) ? OverlapIteratorState(Sub.top) : state
  # if we are not computing overlaps from a particular subobj, 
  if isnothing(state.curr_subobj) # pick the next subobj
    isnothing(state.maps) || error("Inconsistent overlapiterator state")
    if isempty(state.subobject_state)
      return nothing
    else 
      state.curr_subobj = hom(popfirst!(state.subobject_state))
      return Base.iterate(Sub, state)
    end
  elseif isnothing(state.maps) # compute all the maps out of curr subobj
    subobj = state.curr_subobj
    abs_subobj = abstract_attributes(dom(subobj)) ⋅ subobj
    Y = dom(abs_subobj)
    # don't repeat work if already computed syms/maps for something iso to Y
    for res in state.seen
      σ = isomorphism(Y, apex(res))
      if !isnothing(σ)
        state.subobj = nothing
        return (Multispan(map(m->σ⋅m, res)), state)
      end
    end
    maps = Vector{ACSetTransformation}[[abs_subobj]]
    # Compute the automorphisms so that we can remove spurious symmetries
    syms = isomorphisms(Y, Y)
    # Get monic maps from Y into each of the objects. The first comes for free
    maps = Vector{ACSetTransformation}[[abs_subobj]]
    for X in Sub.others
      fs = homomorphisms(Y, X; monic=true)
      real_fs = Set() # quotient fs via automorphisms of Y
      for f in fs 
        if all(rf->all(σ -> force(σ⋅f) != force(rf),  syms), real_fs)  
          push!(real_fs, f)
        end
      end
      if isempty(real_fs)
        break # this subobject of Xs[1] does not have common overlap w/ all Xs
      else
        push!(maps,collect(real_fs))
      end
    end
    if length(maps) == length(Sub.others) + 1
      state.maps = Iterators.Stateful(Iterators.product(maps...))
    else 
      state.curr_subobj = nothing
    end
    return Base.iterate(Sub, state)
  elseif isempty(state.maps)
    state.maps = nothing; state.curr_subobj = nothing
    return Base.iterate(Sub, state)
  else 
    return (Multispan(collect(popfirst!(state.maps))), state)
  end
end

partial_overlaps(Xs::Vector{T}) where T<:ACSet = OverlapIterator(Xs)
partial_overlaps(Xs::ACSet...) = Xs |> collect |> partial_overlaps

""" Compute the Maximimum Common C-Sets from a vector of C-Sets.

Find an ACSet ```a`` with maximum possible size (``|a|``) such that there is a  
monic span of ACSets ``a₁ ← a → a₂``. There may be many maps from this overlap 
into each of the inputs, so a Vector{Vector{ACSetTransformations}} per overlap 
is returned (a cartesian product can be taken of these to obtain all possible 
multispans for that overlap). If there are multiple overlaps of equal size, 
these are all returned.

If there are attributes, we ignore these and use variables in the apex of the 
overlap.
"""
function maximum_common_subobject(Xs::Vector{T}) where T <: ACSet
  it = partial_overlaps(Xs)
  osize = -1
  res = DefaultDict(()->[])
  for overlap in it 
    apx = apex(overlap)
    size = total_parts(apx)
    osize = osize == -1 ? size : osize
    if size < osize return res end 
    push!(res[apx], overlap)
  end 
  return res
end
maximum_common_subobject(Xs::T...) where T <: ACSet = maximum_common_subobject(collect(Xs))

end

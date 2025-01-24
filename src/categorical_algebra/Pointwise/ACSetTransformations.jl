module ACSetTransformations 
export ACSetMorphism, ACSetTransformation, CSetTransformation, 
  StructACSetTransformation,StructTightACSetTransformation, TightACSetTransformation,
  LooseACSetTransformation, components, type_components, coerce_component, 
  coerce_attrvar_component, naturality_failures, show_naturality_failures,
  is_monic, is_epic, force, is_natural, in_bounds

using StructEquality 
using ACSets, CompTime
using ACSets.DenseACSets: attrtype_type

using ....BasicSets, ...SetCats
import ....BasicSets: force, is_monic, is_epic
import ...Cats: components, is_natural

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
                          nparts(X,c), nparts(Y,c); kw[c]...)
  end)
  acomps = NamedTuple(map(attrtypes(S)) do c
    c => coerce_attrvar_component(c, get(components, c, 1:0), 
          TypeSet(X, c), TypeSet(Y, c), nparts(X,c), nparts(Y,c); kw[c]...)
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
  SetFunctions.show_domains(io, α)
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

end # module


""" Transformation between attributed C-sets.

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
limits and colimits in these categories, see [`ACSetTight`](@ref)
and [`ACSetLoose`](@ref).
"""
module ACSetTransformations 

export ACSetTransformation, StructACSetTransformation, 
       DynamicACSetTransformation, components, naturality_failures,
       show_naturality_failures, is_cartesian, in_bounds, 
       is_natural # import from elsewhere, later

using StructEquality

using ACSets, CompTime

using ...BasicSets, ...SetCats
import ....Theories: dom, codom
import ...BasicSets: force, is_monic, is_epic, preimage


""" Transformation between attributed C-sets.

Subtypes of ACSetTransformation contain some (pointwise) SetFunctions
relating two ACSets. This data can only be interpreted in the context of some
category, such as the category of C-Sets, the category of ACSets with tight
transformations, VarACSets, the category of C-Par. In each case there may be
restrictions on what type of data is permitted in the components, but that
validation should happen elsewhere.
"""
abstract type ACSetTransformation end

components(α::ACSetTransformation) = α.components

"""
ACSetTransformation where schema is known at compile time, which can be used for 
performance optimizations.
"""
@struct_hash_equal struct StructACSetTransformation{
    S <: TypeLevelSchema, Comp <: NamedTuple, Dom <: StructACSet{S},
    Codom <: StructACSet{S}} <: ACSetTransformation
  components::Comp
  dom::Dom
  codom::Codom  

  function StructACSetTransformation{S}(components, X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    components = coerce_components(S,components,X,Y)
    new{S,typeof(components),Dom,Codom}(components, X, Y)
  end
end

"""
ACSeTransformation where schema not known at compile time.
"""
@struct_hash_equal struct DynamicACSetTransformation <: ACSetTransformation
  components::NamedTuple
  dom::ACSet
  codom::ACSet

  function DynamicACSetTransformation(components, X, Y) 
    S = acset_schema(X)
    components = coerce_components(S,components,X,Y)
    new(components, X, Y)
  end
end

# Other methods
###############

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
  # show_domains(io, α) # TODO
  print(io, ")")
end

type_components(α::StructACSetTransformation{S}) where S =
  NamedTuple(c => α.components[c] for c in attrtypes(S))

is_monic(α::ACSetTransformation) = all(is_monic, components(α))

is_epic(α::ACSetTransformation) = all(is_epic, components(α))

force(α::ACSetTransformation) = map_components(force, α)

# Other constructors
####################

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
  T = is_struct ? StructACSetTransformation{S} : DynamicACSetTransformation
  return T(merge(ocomps,acomps), X, Y)
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


# Component coercion
#####################

"""
Interpret raw vectors in standard ways to produce FinDomFunctions.
"""
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
function coerce_component(ob::Symbol, f::FinFunction,
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

coerce_component(x::Symbol, f::T, dom_size::Int, codom_size::Int; kw...) where {T<:AbstractVector{<:Integer}}= begin 
  @show x 
  @show f 
  @show dom_size 
  FinFunction(f, dom_size, codom_size; kw...)
end

""" Coerce VarFunction to a SetFunction """
function coerce_attrvar_component(ob::Symbol, f::VarFunction,::TypeSet{T}, ::TypeSet{T},
  dom_size::Int, codom_size::Int; kw...) where {T}
  SetFunction(f)
end

function coerce_attrvar_component(
    ob::Symbol, f::AbstractVector,::TypeSet{T}, ::TypeSet{T},
    dom_size::Int, codom_size::Int; kw...) where {T}
  e = "Domain error in component $ob variable assignment $(length(f)) != $dom_size"
  length(f) == dom_size || error(e)
  return VarFunction{T}(f, FinSet(codom_size))
end


"""Coerce an arbitrary julia function to a LooseVarFunction assuming no variables"""
function coerce_attrvar_component(ob::Symbol, f::Function, d::TypeSet{T},cd::TypeSet{T′},
  dom_size::Int, codom_size::Int; kw...) where {T,T′}
  dom_size == 0 || error("Cannot specify $ob component with $f with $dom_size domain variables")
  coerce_attrvar_component(ob, LooseVarFunction{T,T′}([], f, FinSet(codom_size)), 
                           d, cd, dom_size,codom_size)
end


# function coerce_type_component(type::Symbol, f::SetFunction,
#                                dom_type::Type, codom_type::Type)
#   dom_type <: eltype(dom(f)) || error("Domain error in component $type")
#   eltype(codom(f)) <: codom_type || error("Codomain error in component $type")
#   return f
# end
# function coerce_type_component(type::Symbol, ::Nothing,
#                                dom_type::Type, codom_type::Type)
#   codom_type == Nothing || error("Codomain error in component $type")
#   ConstantFunction(nothing, TypeSet(dom_type))
# end
# coerce_type_component(type::Symbol, f, dom_type::Type, codom_type::Type) =
#   SetFunction(f, TypeSet(dom_type), TypeSet(codom_type))

# Naturality
############
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
function is_natural(α::ACSetTransformation)
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
  S = acset_schema(X)
  α(o::Symbol, i) = comps[o](i)
  ks = keys(comps)
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

naturality_failures(α::ACSetTransformation) =
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

show_naturality_failures(io::IO, α::ACSetTransformation) =
  show_naturality_failures(io, naturality_failures(α))

show_naturality_failures(α::ACSetTransformation) =
  show_naturality_failures(stdout, α)


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

# Cartesian morphisms of acsets
###############################
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
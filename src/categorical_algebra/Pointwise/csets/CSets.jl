export ACSetCategory, ACSetTransformation, sets, naturality_failures, is_natural, 
       show_naturality_failures, get_ob, get_hom, get_op, get_attrtype, get_attr, pre, post, get_op_fn, get_fn, coerce_op,
      ThACSetCategory, entity_cat, attr_cat, prof_cat, map_components,  coerce_hom,
      coerce, coerce_ob, coerce_attr, coerce_components, sets, is_cartesian, entity_attr_cat

using Base.Iterators: flatten
using Reexport
using StructEquality

@reexport using ACSets
import ACSets: TypeLevelBasicSchema, acset_schema, attrtype, constructor
import ACSets.DenseACSets: attrtype_type, attr_type

@reexport using ....ACSetsGATsInterop

using GATlab

using ....Theories, ....BasicSets
import ....Theories: id, compose
import ....BasicSets: SetOb, SetFunction, force, is_monic, is_epic, is_iso, ≃
using ...Cats, ...SetCats
import ...Cats: FinDomFunctor, obtype, homtype, obtype, homtype, get_ob, 
                get_hom, is_natural, naturality_failures
using ..ACSetTransformations, .Heteromorphisms
using ..ACSetTransformations: _ACSetTransformation
import ..ACSetTransformations: ACSetTransformation, get_fn, get_set, get_op_fn, 
                               get_attrtype, coerce_hom, coerce_op, attr_cat

"""
A theory for systematically taking instances of ACSets interpreting them as
diagrams in a concrete semantics category. We will assume some structure to this
category: it is the collage of a profunctor 𝒞 → Σᵢ𝒟ᵢ. The sum is indexed by
the set of symbols of AttrType names (e.g. Weight, Label). We'll assume the 
faithful functor into Set sends objects in 𝒞 to FinSets and objects in each 𝒟ᵢ
to EitherSets where the left values (variables) are finite and right values are 
potentially infinite.

We use the category structures of 𝒞 and 𝒟ᵢ to automatically derive notions of
ACSet morphisms (natural transformations between diagrams) and colimits
(computed pointwise) and limits (computed pointwise, but only possible if 𝒟 is
empty).

We need to convert from ACSets to diagrams in the collage, so this means methods
which take an ACSet + entity name and return an Ob (respectively for generating
hom names and Hom, etc.). We also need to go the other direction.

We can refer to generators in the schema profunctor with symbols.
"""
@theory ThACSetCategory begin 
  # Fixed Types
  #-------------------------
  Sym::TYPE{Symbol}; # how one specifies ob/hom generators in the schema profunctor
  Any′::TYPE{Any};   # anything a user might throw at you which must be interpreted
  ACS::TYPE{ACSet};  # ACSet
  ACSHom::TYPE{ACSetTransformation};  # ACSetTransformation
  Cat::TYPE{ConcreteCategory}
  Hetero::TYPE{ConcreteHeteroMorphism}

  # Types which vary between different models
  #------------------------------------------
  Ob::TYPE;   # Julia type of objects in semantics domain category
  Hom::TYPE;  # Julia type of morphisms in semantics domain category 
  # EntityCat::TYPE; # type whose terms are ThConcreteCategory{<:Ob,<:Hom} models

  # The following are parameterized by schema AttrType, e.g. Weight, Label
  AttrType(type::Sym)::TYPE; # type whose terms are ThConcreteCategory{<:Ob,<:Hom} models
  Op(type::Sym)::TYPE; # type of morphisms in semantics cod cat
  # AttrCat(type::Sym)::TYPE;

  Attr(type::Sym)::TYPE # Julia type of heteromorphisms into 𝒟ᵢ

  # Interpreting the data from the ACSet as living in some collage category
  #------------------------------------------------------------------------
  entity_cat()::Cat
  attr_cat(type::Sym)::Cat
  prof_cat(type::Sym)::Hetero
  
  # An empty ACSet (useful for implementation details e.g. indexing)
  #-----------------------------------------------------------------
  constructor()::ACS 

  # Interpret user-friendly ACSetTransformation data in an intuitive way
  #---------------------------------------------------------------------
  coerce_hom(f::Any′, d::Ob, cd::Ob)::Hom
  coerce_op(f::Any′, d::AttrType(t), cd::AttrType(t))::Op(t) ⊣ [t::Sym]

  # Extracting Ob/Hom data from an ACSet data structure
  #-----------------------------------------------------
  get_ob(x::ACS, o::Sym)::Ob # extract_ob
  get_hom(x::ACS, h::Sym)::Hom # extract_hom
  get_attrtype(x::ACS, a::Sym)::AttrType(a)
  get_op(x::ACS, a::Sym)::Op(a)

  # Below should actually return `Attr(codom(h))`. This is an artifact of using 
  # `Symbol` instead of actually representing the shape category. Fixable, 
  # probably doesn't pose a problem since we don't dispatch on output types.
  get_attr(x::ACS, h::Sym)::Attr(h) 
end

ThACSetCategory.Meta.@wrapper ACSetCategory

ACSetCategory(x::ACSet) = infer_acset_cat(x)

# Other methods
###############
function coerce_hom(C::ACSetCategory, f::ACSetTransformation, x::Symbol) 
  coerce_hom(C, f[x], get_ob(C, dom(f), x), get_ob(C, codom(f), x))
end

function coerce_op(C::ACSetCategory, f::ACSetTransformation, x::Symbol) 
  T = (context = (t = x,),)#attrtype_type(dom(f), x),),)
  coerce_op(C, f[x], get_attrtype(C, dom(f), x), get_attrtype(C, codom(f), x); T...)
end


# function get_fn(C::ACSetCategory, f::ACSetTransformation, x::Symbol)::FinDomFunction
#   get_fn(C, coerce_hom(C, f, x), get_ob(C, dom(f), x), get_ob(C, codom(f), x))
# end

# function get_op_fn(C::ACSetCategory, f::ACSetTransformation, x::Symbol) ::FinDomFunction
#   T = (context = (t = attrtype_type(dom(f), x),),)
#   d, cd = get_attrtype(C, dom(f), x), get_attrtype(C, codom(f), x)
#   get_op_fn(C, coerce_op(C, f, x), d, cd; T...)
# end

""" 
Apply coerce_ob and coerce_attr to the components of an ACSetTransformation.
Any keys not present will be interpreted as `nothing`.
"""
function coerce(f::ACSetTransformation; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(f) : cat
  X, Y, S = dom(f), codom(f), acset_schema(cat)
  comps = Dict(map(ob(S)) do o
    o => coerce_hom(cat, get(components(f), o, nothing), 
                        get_ob(cat, X, o), get_ob(cat, Y, o))
  end)
  attr_comps = Dict(map(attrtypes(S)) do o
    o => coerce_op(cat, get(components(f), o , nothing),
                        get_attrtype(cat, X, o), 
                        get_attrtype(cat, Y, o); 
                        context=(t=o,))
  end)
  _ACSetTransformation(merge(comps,attr_comps), X, Y)
end

""" 
Apply coerce_ob and coerce_attr to the components of an ACSetTransformation.

Does not require that all schema ob and attrtypes are present in `f`.
"""
function coerce_components(f::ACSetTransformation; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(f) : cat
  X, Y, S = dom(f), codom(f), acset_schema(cat)
  comps = Dict(map(collect(pairs(components(f)))) do (k ,v)
    k => if k ∈ ob(S)
      coerce_hom(cat, v, get_ob(cat, X, k), get_ob(cat, Y, k))
    elseif k ∈ attrtypes(S)
      coerce_op(cat, v, attrtype_type(X, k),
                  get_attrtype(cat, X, k), get_attrtype(cat, Y, k))
    end
  end)
  _ACSetTransformation(comps, X, Y)
end

acset_schema(a::ACSetCategory) = acset_schema(constructor(a))

""" When we don't know whether `o` is an Ob or an AttrType in the schema """
entity_attr_cat(a::ACSetCategory, o::Symbol) = if o ∈ ob(acset_schema(a))
  entity_cat(a)
else 
  attr_cat(a, o)
end
  
SetOb(x::ACSet, a::GATExpr{:generator}, c::ACSetCategory) = SetOb(x, nameof(a), c)

function SetOb(x::ACSet, a::Symbol, c::ACSetCategory)
  S = acset_schema(c)
  a ∈ ob(S) && return get_ob(c, x, a)
  a ∈ attrtypes(S) && return get_attr(c, x, a)
  error("$a not found in schema $S")
end

""" C-set → named tuple of sets.
"""
function sets(X::ACSet; cat=nothing) 
  cat=  isnothing(cat) ? infer_acset_cat(X) : cat
  NamedTuple(c => get_ob(cat, X, c) for c in types(acset_schema(X)))
end


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
function is_natural(α::ACSetTransformation; cat::Union{Nothing,ACSetCategory}=nothing)
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  fails = naturality_failures(dom(α), codom(α), components(α); cat)
  all(isempty, last.(collect(fails)))
end

"""
Returns a dictionary whose keys are contained in the names in `arrows(S)`
and whose value at `:f`, for an arrow `(f,c,d)`, is a lazy iterator
over the elements of X(c) on which α's naturality square
for f does not commute. Components should be a NamedTuple or Dictionary
with keys contained in the names of S's morphisms and values vectors or dicts
defining partial functions from X(c) to Y(c).
"""
function naturality_failures(X::ACSet, Y::ACSet, comps; cat=nothing)
  S = acset_schema(X)
  C = isnothing(cat) ? infer_acset_cat(X) : cat
  α(o::Symbol, i) = comps[o](i)
  ks = keys(comps)
  𝒞, 𝒫 = entity_cat(C), t -> prof_cat(C, t)
  hom_arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, homs(S))
  ps = Iterators.map(hom_arrs) do (f, c, d)
    αY₂ = compose[𝒞](comps[c], get_hom(C, Y, f))
    X₁α = compose[𝒞](get_hom(C, X, f), comps[d])
    Pair(f, [(i, αY₂(i), X₁α(i)) for i in parts(X,c) if X₁α(i) != αY₂(i)])
  end

  attr_arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, attrs(S))  

  ps2 = Iterators.map(attr_arrs) do (f, c, d)
    X₁α = hom_map[𝒫(d)](post[𝒫(d)](get_attr(C, X, f), comps[d]))
    αY₂ = hom_map[𝒫(d)](pre[𝒫(d)](comps[c], get_attr(C, Y, f)))
    errs = filter(((_, x, y),) -> x != y, map(parts(X,c)) do i
      lft = αY₂(Left(i))
      rght = X₁α(Left(i))
      (i, getvalue(lft), getvalue(rght))
    end) 
    Pair(f, errs)
  end
  Dict(ps ∪ ps2)
end

function naturality_failures(α::ACSetTransformation; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  naturality_failures(dom(α), codom(α), α.components; cat)
end

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

force(α::ACSetTransformation; cat=nothing) = map_components(force, α; cat)

function map_components(f, α::ACSetTransformation; cat=nothing) 
  new_comps = map(f, components(α))
  ACSetTransformation(new_comps, dom(α), codom(α); cat)
end

function ≃(f::ACSetTransformation, g::ACSetTransformation; cat=nothing) 
  cat = isnothing(cat) ? infer_acset_cat(f) : cat
  S = acset_schema(cat)
  for o in types(S)
    if f[o] isa Union{FinDomFunction, FinFunction} && g[o] isa Union{FinDomFunction, FinFunction}
      f[o] ≃ g[o] || return false
    else 
      f[o] == g[o] || return false
    end
  end
  return true
end

# Cartesian morphisms of acsets
###############################

function is_cartesian_at(f::ACSetTransformation,h::Symbol; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(f) : cat
  𝒞 = entity_cat(cat)
  X,Y,S = dom(f),codom(f),acset_schema(f)
  mor,x,y = h,dom(S,h),codom(S,h)
  s = Span(get_hom(cat, X,mor),f[x])
  c = Cospan(f[y],get_hom(cat, Y,mor))
  L = limit[𝒞](c)
  f = universal[𝒞](L,s)
  is_iso(f)
end

"""    is_cartesian(f,hs)

Checks if an acset transformation `f` is cartesian at the homs in the list `hs`.
Expects the homs to be given as a list of `Symbol`s.
"""
is_cartesian(f,hs=homs(acset_schema(dom(f)),just_names=true)) = 
  all(h->is_cartesian_at(f,h),hs)

# Monic and epic morphisms
##########################
""" infer acset cat by default """
function is_monic(α::ACSetTransformation; cat=nothing) 
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  is_monic[cat](α)
end 

""" infer acset cat by default """
function is_epic(α::ACSetTransformation; cat=nothing) 
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  is_epic[cat](α)
end 

""" infer acset cat by default """
function is_iso(α::ACSetTransformation; cat=nothing) 
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  is_monic(α; cat) && is_epic(α; cat)
end 



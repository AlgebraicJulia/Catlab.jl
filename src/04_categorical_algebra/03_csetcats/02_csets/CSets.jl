export ACSetCategory, ACSetTransformation, sets, naturality_failures, is_natural, 
       show_naturality_failures, get_ob, get_hom, get_op, get_attrtype, get_attr, pre, post,
      ThACSetCategory, entity_cat, attr_cat, prof_cat, map_components, infer_acset_cat, coerce

using Base.Iterators: flatten
using Reexport
using StructEquality

@reexport using ACSets
import ACSets: TypeLevelBasicSchema, acset_schema, attrtype, constructor
import ACSets.DenseACSets: attrtype_type

@reexport using ....ACSetsGATsInterop

using GATlab

using ....Theories, ....BasicSets
import ....Theories: id, compose
import ....BasicSets: SetOb, SetFunction, force

using ...Cats
import ...Cats: FinDomFunctor, obtype, homtype, obtype, homtype, get_ob, get_hom, is_natural
using ..ACSetTransformations
using ..ACSetTransformations: _ACSetTransformation
import ..ACSetTransformations: ACSetTransformation



"""
A theory for systematically taking instances of ACSets and producing a diagram
in a category (in particular: a category which is the collage of a profunctor).

In general, because ACSets don't support operations (i.e. the codomain
"attribute category" is discrete), the `Op` type will usually be trivial.

Although we could be very strict (requiring entity category to be the category
of sets and functions), we adopt a liberal approach where the entity category
and attribute category are unspecified, although methods must be provided to
convert these Obs/AttrTypes into FinSets (likewise for Homs/Attrs into
FinFunctions) in order to understand diagrams into these categories as giving
ACSets.
"""
@theory ThACSetCategory begin 
  EntityCat::TYPE; AttrCat::TYPE; ProfCat::TYPE
  Ob::TYPE;Hom::TYPE; AttrType::TYPE; Op::TYPE; Attr::TYPE
  Sym::TYPE; ACS::TYPE; ACSHom::TYPE; SetType::TYPE; FnType::TYPE

  # Interpreting the data from the ACSet as living in some collage category
  entity_cat()::EntityCat
  attr_cat()::AttrCat
  prof_cat()::ProfCat
  
  # An empty ACSet (has implementation details e.g. indexing)
  constructor()::ACS 

  # Interpret user-friendly hom data in an intuitive way
  coerce(f::ACSHom)::ACSHom 

  # Extracting Ob/Hom data from an ACSet data structure
  get_ob(x::ACS, o::Sym)::Ob
  get_hom(x::ACS, h::Sym)::Hom
  get_attrtype(x::ACS, a::Sym)::AttrType
  get_op(x::ACS, a::Sym)::Op
  get_attr(x::ACS, h::Sym)::Attr

  # Recovering ACSet data (FinSets and FinFunctions) out of Ob/Hom types
  get_set(x::Ob)::SetType;
  get_fn(x::Hom)::FnType;
  get_attr_set(x::AttrType)::SetType;
  get_attr_fn(x::Attr)::FnType;
end

ThACSetCategory.Meta.@wrapper ACSetCategory

# Other methods
###############

acset_schema(a::ACSetCategory) = acset_schema(constructor(a))
  
SetOb(x::ACSet, a::GATExpr{:generator}, c::ACSetCategory) = SetOb(x, nameof(a), c)

function SetOb(x::ACSet, a::Symbol, c::ACSetCategory)
  S = acset_schema(c)
  a ∈ ob(S) && return get_ob(c, x, a)
  a ∈ attrtypes(S) && return get_attr(c, x, a)
  error("$a not found in schema $S")
end

""" C-set → named tuple of sets.
"""
sets(X::ACSet, C::ACSetCategory) = 
  NamedTuple(c => get_ob(C, X, c) for c in types(acset_schema(C)))

FinDomFunctor(acs::ACSet) = FinDomFunctor(acs, ACSetCategory(acs))



# Must be implemented after the pointwise cats are defined
infer_acset_cat(f::ACSetTransformation) = 
  infer_acset_cat(components(f), dom(f), codom(f))


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
  𝒞, 𝒟 = entity_cat(C), attr_cat(C)
  hom_arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, homs(S))

  ps = Iterators.map(hom_arrs) do (f, c, d)
    αY₂ = compose[𝒞](comps[c], get_hom(C, Y, f))
    X₁α = compose[𝒞](get_hom(C, X, f), comps[d])
    Pair(f, [(i, αY₂(i), X₁α(i)) for i in parts(X,c) if X₁α(i) != αY₂(i)])
  end

  attr_arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, attrs(S))  

  ps2 = Iterators.map(attr_arrs) do (f, c, d)
    X₁α = attr_postcompose(C, get_attr(C, X, f), comps[d])
    αY₂ = attr_precompose(C, comps[c], get_attr(C, Y, f))
    Pair(f, [(i, αY₂(i), X₁α(i)) for i in parts(X,c) if X₁α(i) != αY₂(i)])
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

map_components(f, α::ACSetTransformation; cat=nothing) =
  ACSetTransformation(map(f, components(α)), dom(α), codom(α); cat)

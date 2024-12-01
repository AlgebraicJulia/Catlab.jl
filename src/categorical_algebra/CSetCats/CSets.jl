""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetCategory, sets, naturality_failures, is_natural, 
       show_naturality_failures, get_attrtype, get_attr, attrid, opcompose

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
import ....BasicSets: SetOb, SetFunction

using ...Cats
import ...Cats: FinDomFunctor, obtype, homtype, obtype, homtype, get_ob, get_hom
using ..ACSetTransformations
using ..ACSetTransformations: _ACSetTransformation
import ..ACSetTransformations: ACSetTransformation



# Upstream to ACSets.jl
#######################

""" Convert a Schema to a Type-level schema """
TypeLevelBasicSchema(s::BasicSchema{Name}) where {Name} = 
  TypeLevelBasicSchema{Name, Tuple{s.obs...}, Tuple{s.homs...}, 
                       Tuple{s.attrtypes...}, Tuple{s.attrs...}, Tuple{s.eqs...}}

TypeLevelBasicSchema(s::Type{<:TypeLevelBasicSchema}) = s

# Categories of ACsets
######################

"""
Collage of a profunctor - i.e. two copies of ThCategory, along with 
heteromorphisms which can be composed on either side.
"""
@theory ThProfunctorCollage <: ThCategory begin
  AttrType::TYPE;
  Op(opdom::AttrType, opcod::AttrType)::TYPE; 
  Attr(attrdom::Ob,attrcod::AttrType)::TYPE
  attrid(a::AttrType)::Op(a,a)
  opcompose(f::Op(a,b),g::Op(b,c))::Op(a,c) ⊣ [(a,b,c)::AttrType]
  attr_precompose(f::Hom(a,b), g::Attr(b,c))::Attr(a,c) ⊣ [(a,b)::Ob, c::AttrType]
  attr_postcompose(f::Attr(a,b), g::Op(b,c))::Attr(a,c) ⊣ [a::Ob, (b,c)::AttrType]
end

"""
A theory for systematically taking instances of ACSets and producing a diagram 
in a category (in particular: a category which is the collage of a profunctor).

`Ob` is Julia type where schema Ob objects are sent to (e.g. FinSet)
`AttrType` is Julia type where schema AttrType objects are sent to (e.g. TypeSet or VarSet)
`Attr` is the type of heteromorphisms
"""
@theory ThACSetCategory <: ThProfunctorCollage begin 
  Sym::TYPE; ACS::TYPE; ACSHom::TYPE;
  constructor()::ACS
  coerce(f::ACSHom)::ACSHom
  get_ob(x::ACS, o::Sym)::Ob
  get_hom(x::ACS, h::Sym, a::Ob, b::Ob)::Hom(a, b)
  get_attrtype(x::ACS, a::Sym)::AttrType
  get_attr(x::ACS, h::Sym, a::Ob, b::AttrType)::Attr(a,b)
end

"""
"""
abstract type ACSetCategoryImpl{O,H,AT,A} <: Model{
  Tuple{O, H, AT, A, Symbol, ACSet, ACSetTransformation}} end

# Wrapper type for models of ThACSetCategory
#######################################
@struct_hash_equal struct ACSetCategory{S}
  impl::ACSetCategoryImpl
  function ACSetCategory(i::ACSetCategoryImpl{O,H,AT,A}) where {O,H,AT,A}
    implements(i, ThACSetCategory) || error("Bad model $i")
    new{TypeLevelBasicSchema(acset_schema(i))}(i)
  end
end

GATlab.getvalue(f::ACSetCategory) = f.impl

# Access model methods
######################

constructor(i::ACSetCategory) = ThACSetCategory.constructor[getvalue(i)]()

coerce(i::ACSetCategory, f::ACSetTransformation) = 
  ThACSetCategory.coerce[getvalue(i)](f)

id(i::ACSetCategory, x) = ThACSetCategory.id[getvalue(i)](x)

compose(i::ACSetCategory, x, y) = ThACSetCategory.compose[getvalue(i)](x, y)

attrid(i::ACSetCategory, x) = ThACSetCategory.attrid[getvalue(i)](x)

opcompose(i::ACSetCategory, x) = ThACSetCategory.opcompose[getvalue(i)](x)

attr_postcompose(i::ACSetCategory, f, g) = ThACSetCategory.attr_postcompose[getvalue(i)](f, g)

attr_precompose(i::ACSetCategory, f, g) = ThACSetCategory.attr_precompose[getvalue(i)](f, g)


get_ob(i::ACSetCategory, x::ACSet, s::Symbol) = 
  ThACSetCategory.get_ob[getvalue(i)](x, s)

get_hom(i::ACSetCategory, x::ACSet, s::Symbol, a, b) = 
  ThACSetCategory.get_hom[getvalue(i)](x, s, a, b)

get_hom(i::ACSetCategory{S}, x::ACSet, s::Symbol) where S = 
  get_hom(i, x, s, get_ob(i, x, dom(S, s)), get_ob(i, x, codom(S, s)))

get_attrtype(i::ACSetCategory, x::ACSet, s::Symbol) = 
  ThACSetCategory.get_attrtype[getvalue(i)](x, s)

get_attr(i::ACSetCategory, x::ACSet, s::Symbol, a, b) = 
  ThACSetCategory.get_attr[getvalue(i)](x, s, a, b)

get_attr(i::ACSetCategory{S}, x::ACSet, s::Symbol) where S = 
  get_attr(i, x, s, get_ob(i, x, dom(S, s)), get_attrtype(i, x, codom(S, s)))


# Other methods
###############

acset_schema(a::ACSetCategory) = acset_schema(constructor(a))
  
SetOb(x::ACSet, a::GATExpr{:generator}, c::ACSetCategory) = SetOb(x, nameof(a), c)

function SetOb(x::ACSet, a::Symbol, c::ACSetCategory{S}) where S 
  a ∈ ob(S) && return get_ob(c, x, a)
  a ∈ attrtypes(S) && return get_attr(c, x, a)
  error("$a not found in schema $S")
end

""" C-set → named tuple of sets.
"""
sets(X::ACSet, C::ACSetCategory) = 
  NamedTuple(c => get_ob(C, X, c) for c in types(acset_schema(C)))
sets(X::ACSet, C::ACSetCategoryImpl) = sets(X, ACSetCategory(C))

FinDomFunctor(acs::ACSet) = FinDomFunctor(acs, ACSetCategory(acs))


# Misc Implementations
######################
include("MiscImpls/CatsOfACSet.jl")
include("MiscImpls/CodomsOfACSet.jl")
include("MiscImpls/ACSetFunctors.jl")

@reexport using .CatsOfACSet
@reexport using .CodomsOfACSet
@reexport using .ACSetFunctors

# Implementations
#################

include("ACSetCatImpls/CSetCats.jl")
include("ACSetCatImpls/ACSetCats.jl")

@reexport using .CSetCats
@reexport using .ACSetCats

""" The *default* category to interpret an ACSet in """
ACSetCategory(x::ACSet) = ACSetCategory(ACSetCat(x))

# Misc Other methods 
####################
obtype(i::ACSetCategory) = obtype(getvalue(i))

obtype(::ACSetCategoryImpl{O,H,AT,A}) where {O,H,AT,A} = O

homtype(i::ACSetCategory) = homtype(getvalue(i))

homtype(::ACSetCategoryImpl{O,H,AT,A}) where {O,H,AT,A} = H

attrtype_type(i::ACSetCategory) = attrtype_type(getvalue(i))

attrtype_type(::ACSetCategoryImpl{O,H,AT,A}) where {O,H,AT,A} = AT

attrtype(i::ACSetCategory) = attrtype(getvalue(i))

attrtype(::ACSetCategoryImpl{O,H,AT,A}) where {O,H,AT,A} = A

acset_schema(i::ACSetCategoryImpl) = 
  acset_schema(ThACSetCategory.constructor[i]())


""" 
Sensible defaults for interpreting an ACSetTransformation as living in a particular kind of ACSet category 
"""
function infer_acset_cat(comps, X::ACSet, Y::ACSet)::ACSetCategory
  S = acset_schema(X)
  cat = if isempty(attrtypes(S))
    CSetCat
  elseif hasvar(X) || hasvar(Y) 
    VarACSetCat
  else 
    ACSetCat
  end
  return ACSetCategory(cat(X))
end

infer_acset_cat(f::ACSetTransformation) = 
  infer_acset_cat(components(f), dom(f), codom(f))

function hasvar(X::ACSet,x) 
  s = acset_schema(X)
  (x∈ attrs(acset_schema(X),just_names=true) && hasvar(X,codom(s,x))) || 
  x∈attrtypes(acset_schema(X)) && nparts(X,x)>0
end
hasvar(X::ACSet) = any(o->hasvar(X,o), attrtypes(acset_schema(X)))
  
function ACSetTransformation(comps, dom::ACSet, codom::ACSet, 
                             cat::Union{Nothing,ACSetCategory}=nothing)
  cat = isnothing(cat) ? infer_acset_cat(comps, dom, codom) : cat
  return coerce(cat, _ACSetTransformation(comps, dom, codom))
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
function is_natural(α::ACSetTransformation, C::Union{Nothing,ACSetCategory}=nothing)
  C = isnothing(C) ? ACSetCategory(ACSetCat(dom(α))) : C
  fails = naturality_failures(C, dom(α), codom(α), components(α))
  all(isempty, last.(collect(fails)))
end

is_natural(α::ACSetTransformation, C::Category) = is_natural(α, getvalue(C))
is_natural(α::ACSetTransformation, C::TypeCat) = is_natural(α, getvalue(C))
is_natural(α::ACSetTransformation, C::CatOfACSet) = is_natural(α, getvalue(C))


"""
Returns a dictionary whose keys are contained in the names in `arrows(S)`
and whose value at `:f`, for an arrow `(f,c,d)`, is a lazy iterator
over the elements of X(c) on which α's naturality square
for f does not commute. Components should be a NamedTuple or Dictionary
with keys contained in the names of S's morphisms and values vectors or dicts
defining partial functions from X(c) to Y(c).
"""
function naturality_failures(C::ACSetCategory, X::ACSet, Y::ACSet, comps)
  S = acset_schema(X)
  α(o::Symbol, i) = comps[o](i)
  ks = keys(comps)

  hom_arrs = filter(((f,c,d),) -> c ∈ ks && d ∈ ks, homs(S))

  ps = Iterators.map(hom_arrs) do (f, c, d)
    αY₂ = compose(C, comps[c], get_hom(C, Y, f))
    X₁α = compose(C, get_hom(C, X, f), comps[d])
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
  naturality_failures(cat, dom(α), codom(α), α.components)
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

# UNDO
# @cartesian_monoidal_instance ACSet{S} ACSetTransformation{S} CSetCat{S} where S

# @cartesian_monoidal_instance ACSet{S} ACSetTransformation{S} ACSetLoose{S}

# @cocartesian_monoidal_instance ACSet ACSetTransformation CSetCat

# @default_model ThCategory{ACSet, ACSetTransformation} [model::CSetCat]


end # module

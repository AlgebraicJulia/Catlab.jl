""" Functorial data migration for attributed C-sets.
"""
module FunctorialDataMigrations
export SigmaMigration, DeltaMigration, migrate, migrate!,
  representable, yoneda, subobject_classifier, 
  internal_hom, SigmaMigrationFunctor, DeltaMigrationFunctor, 
  DataMigrationFunctor, functor, SimpleMigration, ΔMigration, ΣMigration

using MLStyle: @match
using DataStructures: DefaultDict

using ACSets
using ACSets.DenseACSets: datatypes, attrtype_type
import ACSets.DenseACSets: constructor
using GATlab
using ...Theories: ob, hom, dom, codom, attr, AttrTypeExpr, ⋅
using ..Categories, ..FinCats, ..Limits, ..Diagrams, ..FinSets, ..CSets, ..HomSearch
using ...Graphs, ..FreeDiagrams
import ..Categories: ob_map, hom_map
import GATlab: functor
using ..FinCats: make_map, mapvals, presentation_key
using ..Chase: collage, crel_type, pres_to_eds, add_srctgt, chase, from_c_rel
using ..FinSets: VarSet
using ..CSets: var_reference, sub_vars

# Data types
############

""" A data migration is guaranteed to contain a functor between
schemas that can be used to migrate data between acsets
on those schemas. The
migration may be a pullback data migration ([`DeltaMigration`](@ref)), specified by a
functor ``D → C`` between the schemas, or ``F`` may
be a schema functor specifying a ``Σ`` migration in the covariant direction. Other data migration types are defined in 
`DataMigrations.jl`.
"""
abstract type AbstractDataMigration{F<:FinDomFunctor} end
functor(M::AbstractDataMigration) = M.functor
abstract type ContravariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end
abstract type CovariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end

""" Schema-level functor defining a pullback or delta data migration.

Given a functor ``F: C → D``, the delta migration ``Δ_F`` 
is a functor from ``C``-sets to ``D``-sets that simply sends
a ``C``-set ``X`` to the ``D``-set ``X∘F``.
"""
const DeltaSchemaMigration{F<:FinFunctor} = ContravariantMigration{F}
#This only exists for the acset to acset migrate! method which is performance-optimized for 
#the easy Delta case
struct DeltaMigration{F<:FinFunctor} <: DeltaSchemaMigration{F}
  functor::F
end
""" Sigma or left pushforward functorial data migration between acsets.

  Given a functor ``F: C → D``, the sigma data migration ``Σ_F`` is a functor from
  ``C``-sets to ``D``-sets that is left adjoint to the delta migration functor
  ``Δ_F`` ([`DeltaMigration`](@ref)). Explicitly, the ``D``-set ``Σ_F(X)`` is
  given on objects ``d ∈ D`` by the formula ``Σ_F(x)(d) = \\mathrm{colim}_{F ↓ d}
  X ∘ π``, where ``π: (F ↓ d) → C`` is the projection.
  
  See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
const SigmaSchemaMigration{F<:FinFunctor} = CovariantMigration{F}
struct SigmaMigration{F<:FinFunctor} <: SigmaSchemaMigration{F}
  functor::F
end

""" Contravariantly migrate data from the acset `Y` to a new acset of type `T`.

The mutating variant of this function is [`migrate!`](@ref).
"""
function migrate(::Type{T}, X::ACSet, M::AbstractDataMigration; kw...) where T <: ACSet
  T(migrate(X, M; kw...))
end
function migrate(X::ACSet, M::AbstractDataMigration; kw...)
  migrate(FinDomFunctor(X), M; kw...)
end

""" Contravariantly migrate data from the acset `Y` to the acset `X`.

This is the mutating variant of [`migrate!`](@ref). When the functor on schemas
is the identity, this operation is equivalent to [`copy_parts!`](@ref).
"""
function migrate!(X::ACSet, Y::ACSet, M::AbstractDataMigration; kw...)
  copy_parts!(X, migrate(Y, M; kw...))
end

# Delta migration
#----------------
"""
Apply a ``Δ`` migration by simple precomposition.
"""
migrate(X::FinDomFunctor,M::DeltaSchemaMigration) = X∘functor(M)
migrate(::Type{T}, X::ACSet, M::DeltaMigration) where T <: ACSet =
  migrate!(T(), X, M)

# This seems like there should be an argument to specify it's a Delta
# As we can imagine doing a pushforward with the same syntax
migrate(::Type{T}, X::ACSet, FOb, FHom) where T <: ACSet =
  migrate!(T(), X, FOb, FHom)


# Expected usage is with `X` empty.
function migrate!(X::ACSet, Y::ACSet, M::DeltaMigration)
  S = acset_schema(X)
  F = functor(M)
  partsX = Dict(c => add_parts!(X, c, nparts(Y, nameof(ob_map(F, c))))
                for c in types(S))
  for (f, c, d) in homs(S)
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, hom_map(F, f))])
  end
  for (f, c, _) in attrs(S)
    set_subpart!(X, partsX[c], f, subpart(Y, hom_map(F, f)))
  end
  return X
end

function migrate!(X::ACSet, Y::ACSet, FOb, FHom)
  M = DeltaMigration(FinFunctor(FOb, FHom, FinCat(Presentation(X)), FinCat(Presentation(Y))))
  migrate!(X, Y, M)
end

# On morphisms
migrate(t::Type{T}, f::ACSetTransformation, M::DeltaMigration) where T <: ACSet = 
  migrate(t, f, M.functor)

migrate(t::Type{T}, f::ACSetTransformation, F::FinFunctor) where T <: ACSet = 
  migrate(t, f, ob_map(F), hom_map(F))

function (F::DeltaMigration)(f::ACSetTransformation; T=nothing) 
  T = isnothing(T) ? AnonACSetType(Schema(presentation(dom(functor(F))))) : T
  migrate(T, f, ob_map(F.functor), hom_map(F.functor))
end

function migrate(::Type{T}, f::TightACSetTransformation,
                FOb::AbstractDict, FHom::AbstractDict) where T <: ACSet
  d = Dict()
  for (ob_dom,ob_codom) in pairs(FOb)
    if Symbol(ob_codom) ∈ keys(components(f))
      d[Symbol(ob_dom)] = f[Symbol(ob_codom)]
    end
  end
  Fd, Fcd = migrate(T, dom(f), FOb, FHom), migrate(T, codom(f), FOb, FHom)
  TightACSetTransformation(NamedTuple(d), Fd, Fcd)
end

""" Abstract type for a data migration functor.

This allows a data migration to behave as an actual model of the theory 
of functors with domain and codomain categories of acsets rather than 
schemas, once one knows the exact concrete types Dom and Codom
of the relevant acsets. 
"""
abstract type AbstractMigrationFunctor{Dom<:ACSet,Codom<:ACSet} <:
  Functor{TypeCat{Dom,ACSetTransformation},TypeCat{Codom,ACSetTransformation}} end

ob_map(F::AbstractMigrationFunctor{Dom,Codom}, X) where {Dom,Codom} =
  ob_map(F, Codom, X)

(F::AbstractMigrationFunctor)(X::ACSet) = ob_map(F, X)
(F::AbstractMigrationFunctor)(α::ACSetTransformation) = hom_map(F, α)

"""
Data migration functor given contravariantly. Stores a contravariant migration.
"""
struct DataMigrationFunctor{Dom,Codom,M<:ContravariantMigration} <: AbstractMigrationFunctor{Dom,Codom}
  migration::M
end
migration(F::DataMigrationFunctor) = F.migration

"""
Gives the underlying schema functor of a data migration 
seen as a functor of acset categories.
"""
functor(F::DataMigrationFunctor) = functor(migration(F))

DataMigrationFunctor(migration::ContravariantMigration{F}
                    ) where {F<:Functor{Dom,Codom} where {Dom,Codom}} = 
  DataMigrationFunctor{Dom,Codom,M}(migration)

DataMigrationFunctor(functor::F, ::Type{Dom}, ::Type{Codom}) where {F<:FinFunctor,Dom,Codom} =
  DataMigrationFunctor{Dom,Codom,DeltaMigration{F}}(DeltaMigration(functor))

DataMigrationFunctor(functor::F, ::Type{Codom}) where {F<:FinFunctor,Codom} =
  DataMigrationFunctor{ACSet,Codom,DeltaMigration{F}}(DeltaMigration(functor))

ob_map(F::DataMigrationFunctor, T::Type, X) = migrate(T, X, migration(F))

const DeltaMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:DeltaSchemaMigration}

# Sigma migration
#################

struct SigmaMigrationFunctor{Dom,Codom,M<:SigmaSchemaMigration} <: AbstractMigrationFunctor{Dom,Codom}
  migration::M
  dom_constructor
  codom_constructor
  SigmaMigrationFunctor(f::F,d::ACSet,c::ACSet) where F<:FinFunctor = 
    new{typeof(d),typeof(c),SigmaMigration{F}}(SigmaMigration(f),constructor(d),constructor(c))
end 

migration(F::SigmaMigrationFunctor) = F.migration

functor(F::SigmaMigrationFunctor) = functor(migration(F))

SigmaMigrationFunctor(f,::Type{T},c::ACSet) where T<:StructACSet = 
  SigmaMigrationFunctor(f,T(),constructor(c))

SigmaMigrationFunctor(f, d::ACSet, ::Type{T}) where T<:StructACSet = 
  SigmaMigrationFunctor(f,d,T())

SigmaMigrationFunctor(f,d::Type{T′},::Type{T}
                     ) where {T<:StructACSet, T′<:StructACSet} = 
  SigmaMigrationFunctor(f,d,T())

SigmaMigrationFunctor(f,T,c::ACSet) = 
  SigmaMigrationFunctor(f,T(),constructor(c))

SigmaMigrationFunctor(f, d::ACSet, T) = SigmaMigrationFunctor(f,d,T())

"""
Create a C-Set for the collage of the functor. Initialize data in the domain 
portion of the collage, then run the chase.

When `return_unit` is true, returns the diagram morphism given by the unit of
the adjunction between Σ and Δ migration functors.
"""
# This should be replaced or at least paired with a new migrate function if 
# anybody works on sigma migrations sometime.
# Also, we probably don't want to construct the collage every time we migrate 
# using M, at least it should be possible to cache.
function (M::SigmaMigrationFunctor)(d::ACSet; n=100, return_unit::Bool=false)
  D, CD = M.dom_constructor(), M.codom_constructor()
  F = functor(M)
  S = acset_schema(d)
  # ask the collage to represent a transformation that's natural
  # only on the non-attrtype objects of the domain
  obs = map(x->Ob(FreeSchema.Ob,x), S.obs)
  col, col_pres = collage(functor(M),objects=obs)
  i1, i2 = legs(col)

  # Initialize collage C-Set with data from `d`
  atypes = Dict{Symbol,Type}()
  for (k,v) in datatypes(D)  
    atypes[Symbol(ob_map(i1,k))] = v 
  end
  for (k,v) in datatypes(CD) 
    atypes[Symbol(ob_map(i2,k))] = v 
  end
  # collage ACSet type
  fun_type = AnonACSet(presentation(apex(col)); type_assignment=atypes)
  # collage type where the arrows are replaced with spans
  col_type = crel_type(presentation(apex(col)); types=atypes, name="Sigma")()
  for o in types(S)
    add_parts!(col_type, Symbol(ob_map(i1,o)), nparts(d,o))
  end
  for h in arrows(S; just_names=true)
    s,t = add_srctgt(hom_map(i1,h))
    add_parts!(col_type, Symbol(hom_map(i1,h)), length(d[h]))
    col_type[s] = 1:length(d[h])
    col_type[t] = d[h]
  end 
  # Run chase 
  eds = pres_to_eds(col_pres; types=atypes, name="Sigma")
  chase_rel_res, ok = chase(col_type, eds, n)
  # Postprocess result
  ok || error("Sigma migration did not terminate with n=$n")
  res = CD
  rel_res = codom(chase_rel_res)
  fun_res, ok = from_c_rel(rel_res, fun_type)
  ok || error("Relations are not functional")
  # println("FUN RES")
  # show(stdout,"text/plain",fun_res)
  S′ = acset_schema(fun_res)

  # Handle attribute values (merging, setting explicit values)
  eval_dict = DefaultDict{Symbol, Dict}(() -> Dict())
  merge_dict = DefaultDict{Symbol, DefaultDict{Int,Vector{Int}}}(
    ()->DefaultDict{Int,Vector{Int}}(() -> Int[]))
  for (f, a, _) in attrs(S)
    f′ = hom_map(F⋅i2 , f)
    α = generator(Presentation(S′), Symbol("α_$a"))
    b′ = Symbol(codom(f′))
    for iₐ in parts(d, a)
      val = d[iₐ, f]
      val′ = fun_res[iₐ, α ⋅ f′]
      val′ isa AttrVar || error("Codomain is all attrvars")
      if !(val isa AttrVar)
        eval_dict[b′][val′.val] = val
      else 
        push!(merge_dict[b′][val.val], val′.val)
      end
    end
  end
  # @show eval_dict
  # @show merge_dict
  fun_res = codom(sub_vars(fun_res, eval_dict, 
                  Dict([k=>collect(values(v)) for (k,v) in merge_dict])))

  # Copy data over into result
  res = ΔMigration(i2, constructor(res))(fun_res)


  wandering_vars = Dict(map(attrtypes(S)) do o 
    o′, o′′ = Symbol(ob_map(i1,o)), Symbol(ob_map(F⋅i2,o))
    dic = Dict{Int, AttrVar}()
    for i in parts(rel_res, o′)
      if isnothing(var_reference(fun_res, o′, i))
        add_part!(res, o)
        dic[i] = AttrVar(add_part!(fun_res, o′′))
      end
    end
    o => dic 
  end)

  return_unit || return res

  # @show wandering_vars
  # Return result as DiagramHom{id}.
  diagram_map = Dict{Symbol, Any}(map(ob(S)) do o
    o => FinFunction(fun_res, Symbol("α_$o"))
  end)
  # @show diagram_map
  for o in attrtypes(S)
    o′, o′′ = Symbol.([ob_map(i1, o), ob_map(i2, o)])
    T = attrtype_type(D,o)

    diagram_map[o] = VarFunction{T}(map(parts(fun_res, o′)) do i
      v_r = var_reference(fun_res, o′, i)
      if isnothing(v_r)
        wandering_vars[o][i]
      else
        f1, c1, j = v_r
        c = only([a for a in ob(S) if Symbol(ob_map(i1, a)) == c1])
        f = only([a for a in attrs(S; just_names=true) if 
                  Symbol(last(split_r(hom_map(i1, a)))) == f1])
        f2 = Symbol(last(split_r(hom_map(i2, f))))
        fun_res[diagram_map[c](j), f2]
      end
    end, FinSet(nparts(fun_res, o′′)))
  end
  # @show diagram_map
  # show(stdout,"text/plain",res)
  # println("FinDomFunctor(d) $(FinDomFunctor(d))")
  # println("FinDomFunctor(res) $(FinDomFunctor(res))")

  # Delt = ΔMigration(functor(M), M.dom_constructor)(res)
  # ϕ = FinTransformation(diagram_map, FinDomFunctor(d), FinDomFunctor(Delt))
  # final_res = DiagramHom{id}(functor(M), ϕ, FinDomFunctor(res))
  final_res = DiagramHom{id}(functor(M), diagram_map, FinDomFunctor.([d,res])...)
  # println(codom(final_res.diagram_map))
  is_natural(final_res.diagram_map) || error("HERE")
  final_res
end


# function DiagramHom{id}(f::FinFunctor, components, D::ACSetFunctor, D′::ACSetFunctor;kw...)
#   error("HERE")
#   ϕ = FinTransformation(components, D, f⋅D′)
#   DiagramHom{id}(f, ϕ, D′;kw...)
# end

"""
Split an n-fold composite (n may be 1) 
Hom or Attr into its left n-1 and rightmost 1 components
"""
split_r(f) = head(f) == :compose ?
  (compose(args(f)[1:end-1]),last(f)) : (id(dom(f)),f)


# "Simple" migration functors ... maybe integrable into the above hierarchy 
#--------------------------------------------------------------------------
abstract type SimpleMigration end 

struct ΔMigration <: SimpleMigration
  F::FinFunctor
  constructor
end

functor(m::SimpleMigration) = m.F 
constructor(m::SimpleMigration) = m.constructor

function (F::ΔMigration)(X::ACSet)
  migrate!(constructor(F)(), X, DeltaMigration(functor(F))) # ob_map(functor(F)), hom_map(functor(F)))
end

function (F::ΔMigration)(f::TightACSetTransformation)
  d = Dict()
  for (ob_dom, ob_codom) in pairs(ob_map(functor(F)))
    if haskey(components(f), Symbol(ob_codom))
      d[Symbol(ob_dom)] = f[Symbol(ob_codom)]
    end
  end
  ACSetTransformation(F(dom(f)), F(codom(f)); d...)
end

struct ΣMigration <: SimpleMigration
  F::FinFunctor
  constructor
end

function (M::ΣMigration)(X::ACSet; kw...)::Union{ACSet, DiagramHom}
  SigmaMigrationFunctor(functor(M), X, constructor(M)())(X; kw...)
end

"""
Sigma migration on morphisms begins with migrating the dom, X, and codom, Y.

The new components, e.g. for some object "a" in the schema, are the unique ones
which make the following square commute:

```  
         fₐ
        Xₐ  →  Yₐ        
    αXₐ ↓      ↓ αYₐ
      F(X) ⤑ F(X)'
```

This is because the results of the sigma migrations are freely generated by some 
generators, and we stipulate the homomorphism by saying where the generators go.
"""
function (M::ΣMigration)(f::ACSetTransformation)::ACSetTransformation

  d, cd = Xs = dom(f), codom(f)
  ηs = M.(Xs; return_unit=true)
  αd, αcd = diagram_map.(ηs)
  Fd, Fcd = ACSet.(codom.(ηs))

  S = acset_schema(d)

  initial = DefaultDict{Symbol, Dict{Int, Union{Int, AttrVar}}}(
    () -> Dict{Int, Union{Int, AttrVar}}())
  for o in ob(S)
    Fo = Symbol(ob_map(functor(M), o))
    for i in parts(d, o)
      initial[Fo][αd[o](i)] = αcd[o](f[o](i))
    end
  end
  for o in attrtypes(S)
    Fo = Symbol(ob_map(functor(M), o))
    for i in AttrVar.(parts(d, o))
      initial[Fo][αd[o](i).val] = αcd[o](f[o](i))
    end
  end

  h = homomorphism(Fd, Fcd; initial)
  isnothing(h) &&  show(stdout,"text/plain", d)
  isnothing(h) &&  show(stdout,"text/plain", cd)
  h
end

# Derivative applications of migration functors to other data structures
#-----------------------------------------------------------------------
(m::SimpleMigration)(::Nothing) = nothing

(F::SimpleMigration)(s::Multispan) = Multispan(F(apex(s)), F.(collect(s)))

(F::SimpleMigration)(s::Multicospan) = Multicospan(F(apex(s)), F.(collect(s)))

# Yoneda embedding
#-----------------

""" Construct a representable C-set.

Recall that a *representable* C-set is one of form ``C(c,-): C → Set`` for some
object ``c ∈ C``.

This function computes the ``c`` representable as the left pushforward data
migration of the singleton ``{c}``-set along the inclusion functor ``{c} ↪ C``,
which works because left Kan extensions take representables to representables
(Mac Lane 1978, Exercise X.3.2). Besides the intrinsic difficulties with
representables (they can be infinite), this function thus inherits any
limitations of our implementation of left pushforward data migrations.
"""
function representable(cons, ob::Symbol; return_unit_id::Bool=false)
  C₀ = Presentation{Symbol}(FreeSchema)
  C = Presentation(cons())
  add_generator!(C₀, C[ob])
  X = AnonACSet(C₀); add_part!(X, ob)
  F = FinFunctor(Dict(ob => ob), Dict(), C₀, C)
  ΣF = SigmaMigrationFunctor(F, X, cons())
  if return_unit_id
    η = ΣF(X; return_unit=true)
    (ACSet(diagram(codom(η))), only(collect(diagram_map(η)[ob])))
  else
    ΣF(X)
  end
end

"""
The subobject classifier Ω in a presheaf topos is the presheaf that sends each 
object A to the set of sieves on it (equivalently, the set of subobjects of the 
representable presheaf for A). Counting subobjects gives us the *number* of A 
parts; the hom data for f:A->B for subobject Aᵢ is determined via:

Aᵢ ↪ A 
↑    ↑ f*  
PB⌝↪ B          (PB picks out a subobject of B, up to isomorphism.)

(where A and B are the representables for objects A and B and f* is the unique 
map from B into the A which sends the point of B to f applied to the point of A)

Returns the classifier as well as a dictionary of subobjects corresponding to 
the parts of the classifier.
"""
function subobject_classifier(T::Type; kw...)
  S = Presentation(T())
  isempty(generators(S, :AttrType)) ||
    error("Cannot compute Ω for schema with attributes")
  y = yoneda(T; kw...)
  obs = nameof.(generators(S, :Ob))
  subobs = Dict(ob => subobject_graph(ob_map(y, ob))[2] for ob in obs)
  Ω = T()

  for ob in obs
    add_parts!(Ω, ob, length(subobs[ob]))
  end

  for (f, a, b) in homs(acset_schema(Ω))
    BA = hom_map(y, f)
    Ω[f] = map(parts(Ω, a)) do pᵢ
      Aᵢ = hom(subobs[a][pᵢ])
      _, PB = force.(pullback(Aᵢ, BA))
      return only(filter(parts(Ω, b)) do pⱼ
        Bⱼ = hom(subobs[b][pⱼ])
        any(σ ->  force(σ ⋅ Bⱼ) == PB, isomorphisms(dom(PB),dom(Bⱼ)))
      end)
    end
  end
  return Ω, subobs
end

"""
Objects: Fᴳ(c) = C-Set(C × G, F)    where C is the representable c

Given a map f: a->b, we compute that f(Aᵢ) = Bⱼ by constructing the following:
          Aᵢ
    A × G → F
  f*↑ ↑ ↑ ↗ Bⱼ       find the hom Bⱼ that makes this commute
    B × G 

where f* is given by `yoneda`.
"""
function internal_hom(G::T, F::T; kw...) where T<:ACSet
  S = Presentation(G)
  y = yoneda(T; kw...)
  obs = nameof.(generators(S, :Ob))
  prods = Dict(ob => product(ob_map(y, ob),G) for ob in obs)
  maps = Dict(ob => homomorphisms(apex(prods[ob]),F) for ob in obs)
  Fᴳ = T()

  for ob in obs
    add_parts!(Fᴳ, ob, length(maps[ob]))
  end

  for (f, a, b) in homs(acset_schema(G))
    BA = hom_map(y, f)
    π₁, π₂ = prods[b]
    Fᴳ[f] = map(parts(Fᴳ, a)) do pᵢ
      composite = force(universal(prods[a], Span(π₁⋅BA, π₂)) ⋅ maps[a][pᵢ])
      findfirst(==(composite), maps[b])
    end
  end

  return Fᴳ, homs
end

""" Compute the Yoneda embedding of a category C in the category of C-sets.

Because Catlab privileges copresheaves (C-sets) over presheaves, this is the
*contravariant* Yoneda embedding, i.e., the embedding functor C^op → C-Set.

The first argument `cons` is a constructor for the ACSet, such as a struct acset
type. If representables have already been computed (which can be expensive),
they can be supplied via the `cache` keyword argument.

Returns a `FinDomFunctor` with domain `op(C)`.
"""
function yoneda(cons; cache::AbstractDict=Dict{Symbol,Any}())
  C = Presentation(cons())

  # Compute any representables that have not already been computed.
  for c in nameof.(generators(C, :Ob))
    haskey(cache, c) && continue
    cache[c] = representable(cons, c, return_unit_id=true)
  end

  for c in nameof.(generators(C, :AttrType))
    haskey(cache, c) && continue
    rep = cons()
    cache[c] = (rep, add_part!(rep, c))
  end

  # Object map of Yoneda embedding.
  y_ob = Dict(c => yc for (c, (yc, _)) in pairs(cache))

  # Morphism map of Yoneda embedding.
  y_hom = Dict(Iterators.map(generators(C, :Hom) ∪ generators(C, :Attr)) do f
    c, d = nameof(dom(f)), nameof(codom(f))
    (yc, rootc), (yd, rootd) = cache[c], cache[d]
    initial = Dict(d => Dict(rootd => yc[rootc,f]))
    nameof(f) => homomorphism(yd, yc, initial=initial) # Unique homomorphism.
  end)

  FinDomFunctor(y_ob, y_hom, op(FinCat(C)))
end

yoneda(X::DynamicACSet; kw...) = yoneda(constructor(X); kw...)

# Schema translation
####################

# FIXME: This function does not belong here.

"""   FreeDiagram(pres::Presentation{FreeSchema, Symbol})

Returns a `FreeDiagram` whose objects are the generating objects of `pres` and 
whose homs are the generating homs of `pres`.
"""
function FreeDiagrams.FreeDiagram(pres::Presentation{ThSchema.Meta.T, Symbol})
  obs = Array{FreeSchema.Ob}(generators(pres, :Ob))
  homs = Array{FreeSchema.Hom}(generators(pres, :Hom))
  doms = map(h -> generator_index(pres, nameof(dom(h))), homs)
  codoms = map(h -> generator_index(pres, nameof(codom(h))), homs)
  return FreeDiagram(obs, collect(zip(homs, doms, codoms)))
end

end # module

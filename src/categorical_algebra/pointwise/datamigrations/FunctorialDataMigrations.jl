export SigmaMigration, DeltaMigration, migrate, migrate!,
   SigmaMigrationFunctor, DeltaMigrationFunctor, 
  DataMigrationFunctor, functor

using MLStyle: @match

using ACSets
using ACSets.DenseACSets: datatypes
using GATlab
import GATlab: functor

using ....Theories: ob, hom, dom, codom, attr, AttrTypeExpr, ⋅
using ....Graphs, ....BasicSets, ...Cats
import ...Cats: ob_map, hom_map

using ...Cats.FinCats.FinCatPres: presentation_key

using ..Pointwise
using ..Chase: collage, crel_type, pres_to_eds, add_srctgt


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
abstract type AbstractDataMigration end
functor(M::AbstractDataMigration) = M.functor
abstract type ContravariantMigration <: AbstractDataMigration end
abstract type CovariantMigration <: AbstractDataMigration end

""" Schema-level functor defining a pullback or delta data migration.

Given a functor ``F: C → D``, the delta migration ``Δ_F`` 
is a functor from ``C``-sets to ``D``-sets that simply sends
a ``C``-set ``X`` to the ``D``-set ``X∘F``.
"""
const DeltaSchemaMigration = ContravariantMigration
# This only exists for the acset to acset migrate! method which is 
# performance-optimized for the easy Delta case
struct DeltaMigration <: DeltaSchemaMigration
  functor::FunctorFinDom
end
""" Sigma or left pushforward functorial data migration between acsets.

  Given a functor ``F: C → D``, the sigma data migration ``Σ_F`` is a functor from
  ``C``-sets to ``D``-sets that is left adjoint to the delta migration functor
  ``Δ_F`` ([`DeltaMigration`](@ref)). Explicitly, the ``D``-set ``Σ_F(X)`` is
  given on objects ``d ∈ D`` by the formula ``Σ_F(x)(d) = \\mathrm{colim}_{F ↓ d}
  X ∘ π``, where ``π: (F ↓ d) → C`` is the projection.
  
  See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
const SigmaSchemaMigration = CovariantMigration
struct SigmaMigration <: SigmaSchemaMigration
  functor::FinFunctor
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
migrate(X::FunctorFinDom,M::DeltaSchemaMigration) = X∘functor(M)
migrate(::Type{T}, X::ACSet, M::DeltaMigration) where T <: ACSet =
  migrate!(T(), X, M)

migrate(::Type{T}, X::ACSet, FOb, FHom; homtype=:generator) where T <: ACSet =
  migrate!(T(), X, FOb, FHom; homtype)


#Expected usage is with `X` empty.
function migrate!(X::StructACSet{Sc}, Y::ACSet, M::DeltaMigration) where Sc
  S = Presentation(Sc)
  F = functor(M)
  partsX = Dict(c => add_parts!(X, c, nparts(Y, nameof(ob_map(F,S[c]))))
                for c in ob(Sc))
  for (f,c,d) in homs(Sc)
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, hom_map(F,S[f]))])
  end
  for (f,c,_) in attrs(Sc)
    set_subpart!(X, partsX[c], f, subpart(Y, hom_map(F,S[f])))
  end
  return X
end

function migrate!(X::ACSet, Y::ACSet, FOb, FHom; homtype=:generator)
  F = FinFunctor(FOb, FHom, FinCat(Presentation(X)), FinCat(Presentation(Y)); 
                 homtype)
  migrate!(X, Y, DeltaMigration(F))
end

# On morphisms
migrate(t::Type{T}, f::ACSetTransformation, M::DeltaMigration) where T <: ACSet = 
  migrate(t, f, M.functor)

migrate(t::Type{T}, f::ACSetTransformation, F::FinFunctor) where T <: ACSet = 
  migrate(t, f, ob_map(F), hom_map(F); homtype=:hom)

function migrate(::Type{T}, f::ACSetTransformation,
                FOb::AbstractDict, FHom::AbstractDict; homtype) where T <: ACSet
  d = Dict()
  for (ob_dom,ob_codom) in pairs(FOb)
    if Symbol(ob_codom) ∈ keys(components(f))
      d[Symbol(ob_dom)] = f[Symbol(ob_codom)]
    end
  end
  Fd, Fcd = [migrate(T, X, FOb, FHom; homtype) for X in [dom(f), codom(f)]]
  ACSetTransformation(NamedTuple(d), Fd, Fcd)
end

""" Abstract type for a data migration functor.

This allows a data migration to behave as an actual model of the theory 
of functors with domain and codomain categories of acsets rather than 
schemas, once one knows the exact concrete types Dom and Codom
of the relevant acsets. 
"""
abstract type AbstractMigrationFunctor end

ob_map(F::AbstractMigrationFunctor, X) =
  ob_map(F, Codom, X)

(F::AbstractMigrationFunctor)(X::ACSet) = ob_map(F, X)
(F::AbstractMigrationFunctor)(α::ACSetTransformation) = hom_map(F, α)

"""
Data migration functor given contravariantly. Stores a contravariant migration.
"""
struct DataMigrationFunctor <: AbstractMigrationFunctor
  migration::ContravariantMigration
  Dom::Type
  Codom::Type
end
migration(F::DataMigrationFunctor) = F.migration
ob_map(F::DataMigrationFunctor, X) =
  ob_map(F, F.Codom, X)

"""
Gives the underlying schema functor of a data migration 
seen as a functor of acset categories.
"""
functor(F::DataMigrationFunctor) = functor(migration(F))

# DataMigrationFunctor(migration::ContravariantMigration) = 
#   DataMigrationFunctor(migration)

DataMigrationFunctor(functor::F, ::Type{Dom}, ::Type{Codom}) where {F<:FinFunctor,Dom,Codom} =
  DataMigrationFunctor(DeltaMigration(functor), Dom, Codom)

DataMigrationFunctor(functor::FinDomFunctor, ::Type{Codom}) where Codom =
  DataMigrationFunctor(DeltaMigration(functor))

ob_map(F::DataMigrationFunctor, T::Type, X) = migrate(T, X, migration(F))

const DeltaMigrationFunctor = DataMigrationFunctor

# Sigma migration
#################

struct SigmaMigrationFunctor <: AbstractMigrationFunctor
  migration::SigmaMigration
  dom_constructor
  codom_constructor
  SigmaMigrationFunctor(f::FunctorFinDom,d::ACSet,c::ACSet) = 
    new(SigmaMigration(f),constructor(d),constructor(c))
end 
migration(F::SigmaMigrationFunctor) = F.migration
functor(F::SigmaMigrationFunctor) = functor(migration(F))

SigmaMigrationFunctor(f,::Type{T},c::ACSet) where T<:StructACSet = SigmaMigrationFunctor(f,T(),constructor(c))
SigmaMigrationFunctor(f,d::ACSet,::Type{T}) where T<:StructACSet = SigmaMigrationFunctor(f,d,T())
SigmaMigrationFunctor(f,d::Type{T′},::Type{T}) where {T<:StructACSet, T′<:StructACSet} = SigmaMigrationFunctor(f,T′(),T())
SigmaMigrationFunctor(f,T,c::ACSet)  = SigmaMigrationFunctor(f,T(),constructor(c))
SigmaMigrationFunctor(f,d::ACSet,T)  = SigmaMigrationFunctor(f,d,T())

"""
Create a C-Set for the collage of the functor. Initialize data in the domain 
portion of the collage, then run the chase.

When `return_unit` is true, returns the diagram morphism given by the unit of
the adjunction between Σ and Δ migration functors.
"""
#This should be replaced or at least paired with a new migrate function if anybody works on sigma migrations sometime.
#Also, we probably don't want to construct the collage every time we migrate using M, at least it should
#be possible to cache.
function (M::SigmaMigrationFunctor)(d::ACSet; n=100, return_unit::Bool=false, cat=nothing)
  D,CD = M.dom_constructor(), M.codom_constructor()
  cat = isnothing(cat) ? infer_acset_cat(CD) : cat
  F = functor(M)
  Sc = acset_schema(d)
  S = Presentation(Sc)
  S_codom = Presentation(acset_schema(CD))

  #ask the collage to represent a transformation that's natural
  #only on the non-attrtype objects of the domain
  obs = S.generators[:Ob] #map(x->S[x],Sc.obs)
  col, col_pres = collage(functor(M),objects=obs)
  i1,i2 = legs(col)
  # Initialize collage C-Set with data from `d`
  atypes = Dict{Symbol,Type}()
  for (k,v) in datatypes(D)  atypes[Symbol(ob_map(i1,S[k]))] = v end
  for (k,v) in datatypes(CD) atypes[Symbol(ob_map(i2,S_codom[k]))] = v end
  col_type = crel_type(presentation(getvalue(apex(col))); types=atypes, name="Sigma")()
  for o in types(Sc)
    add_parts!(col_type, Symbol(ob_map(i1,S[o])), nparts(d,o))
  end
  for h in arrows(Sc; just_names=true)
    Sh = S[h]
    s,t = add_srctgt(hom_map(i1,Sh))
    add_parts!(col_type, Symbol(hom_map(i1,Sh)), length(d[h]))
    col_type[s] = 1:length(d[h])
    col_type[t] = d[h]
  end 
  # Run chase 
  eds = pres_to_eds(col_pres; types=atypes, name="Sigma", cat)
  cat2 = ACSetCategory(typeof(getvalue(cat))(col_type))
  chase_rel_res, ok = chase(col_type, eds, n; cat=cat2)
  # Postprocess result
  ok || error("Sigma migration did not terminate with n=$n")
  res = CD
  rel_res = codom(chase_rel_res)
  Sc2 = acset_schema(res)
  S2 = Presentation(Sc2)
  for o in types(Sc2)
    add_parts!(res, o, nparts(rel_res, Symbol(ob_map(i2,S2[o]))))
  end 
  for h in arrows(Sc2;just_names=true)
    hsrc, htgt = add_srctgt(hom_map(i2,S2[h]))
    for (domval, codomval) in zip(rel_res[hsrc], rel_res[htgt])
      res[domval,h] = codomval
    end
  end
  #Go back and make sure attributes that ought to have
  #specific values because of d do have those values.
  for (k, kdom, _) in attrs(Sc)
    f = hom_map(F,S[k])
    #split f into its hom part and its attr part
    f1,f2 = split_r(f)
    #Need f1 on the collage for rel_res but f2 
    #on the target schema
    f1 = hom_map(i2,f1)#S2[f1])
    for i in parts(d,kdom)
      oldval = subpart(d,i,k)
      src_a,tgt_a=add_srctgt(Symbol("α_$kdom"))
      src_f,tgt_f=add_srctgt(Symbol("$f1"))
      #Find where i goes under alpha, and then where that goes
      #under the hom part of f, by walking the spans in rel_res.
      j = rel_res[only(incident(rel_res,i,src_a)),
                  tgt_a] 
      f1j = f1 isa GATExpr{:id} ? j :
       rel_res[only(incident(rel_res,j,src_f)),
              tgt_f]
      res[f1j,nameof(f2)] = oldval
    end
  end
  rem_free_vars!(res)
  return_unit || return res

  # Return result as DiagramHom.
  diagram_map = Dict(map(types(Sc)) do o
    s, t= add_srctgt("α_$o")
    m = last.(sort(collect(zip([rel_res[x] for x in [s,t]]...))))
    F = compose[FinCatC()](functor(M), i2)
    elem = FinFunction(m, nparts(rel_res, nameof(ob_map(F,S[o]))))
    # This is assuming we're working with CSets or VarACSets
    S[o] => o ∈ ob(Sc) ? elem : TaggedElem(elem, S[o])
  end)
  F(x) = DiagramId(FinDomFunctor(x))
  DiagramHom(functor(M), diagram_map, F(d), F(res))
end

"""
Split an n-fold composite (n may be 1) 
Hom or Attr into its left n-1 and rightmost 1 components
"""
split_r(f) = head(f) == :compose ?
  (compose(args(f)[1:end-1]),last(f)) : (id(dom(f)),f)

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
  return FreeDiagram(FreeGraph(obs, collect(zip(homs, doms, codoms))))
end

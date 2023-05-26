""" Functorial data migration for attributed C-sets.
"""
module DataMigrations
export DataMigration, TotalDataMigration, SigmaMigration, DeltaMigration, SigmaMigrationFunctor, 
  DeltaMigrationFunctor, DataMigrationFunctor, functor, migrate, migrate!,  representable, yoneda, colimit_representables

using ACSets
using ACSets.DenseACSets: constructor, datatypes
using ...Present
using ...Theories: ob, hom, dom, codom, attr, AttrTypeExpr
using ..Categories, ..FinCats, ..Limits, ..Diagrams, ..FinSets, ..CSets
using ...Graphs, ..FreeDiagrams
import ..Categories: ob_map, hom_map
using ..FinCats: make_map, mapvals
using ..Chase: collage, crel_type, pres_to_eds, add_srctgt, chase
using ..FinSets: VarSet

# Data types
############

""" Conjunctive query over schema ``C``.

The diagram comprising the query specifies a finite limit.
"""
const ConjQuery{C<:FinCat} = Diagram{op,C}

""" Gluing or agglomerative query over schema ``C``.

The diagram comprising the query specifies a finite colimit. In the important
special case that the diagram has discrete shape, it specifies a finite
coproduct and the query is called "linear" or "disjunctive".
"""
const GlueQuery{C<:FinCat} = Diagram{id,C}

""" "Gluc query" (gluing of conjunctive queries) over schema ``C``.

The diagram of diagrams comprising the query specifies a finite colimit of
finite limits. In the important special case that the outer diagram has discrete
shape, it specifies a finite coproduct of finite limits and the query is called
a "duc query" (disjoint union of conjunctive queries).
"""
const GlucQuery{C<:FinCat} = Diagram{id,<:TypeCat{<:Diagram{op,C}}}

""" A data migration is guaranteed to contain a functor between
schemas that can be used to migrate data between acsets
on those schemas. This functor ``F`` may be partial, in which case
it contains extra data describing how to use it to execute a migration. The
migration may be a pullback data migration ([`DeltaMigration`](@ref)), specified by a
functor ``D → C`` between the schemas, or a conjunctive, gluing,
duc, or gluc (contravariant) data migration. Alternatively, ``F`` may
be a schema functor specifying a ``Σ`` migration in the covariant direction.
"""
abstract type AbstractDataMigration{F<:FinDomFunctor} end
functor(M::AbstractDataMigration) = M.functor
abstract type AbstractContravariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end
abstract type AbstractCovariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end

"""
A contravariant data migration whose functor ``F`` may not be fully defined. Instead,
the migration ``F⋅X`` for an acset ``X`` can only be constructed once we have access
to ``X``'s attribute types. The dictionary of parameters contains anonymous 
functions acting on ``X``'s attributes using Julia functions defined on 
these attribute types.
"""
#The same, except for the supertype and the variance parameter T, as a QueryDiagram in older code.
#(Instead, `C` itself is probably a category of queries, which thus contain the information of T further down.)
struct DataMigration{F<:FinDomFunctor,Params<:AbstractDict} <: AbstractContravariantMigration{F}
  functor::F
  params::Params
end
#This is possibly a bit ugly/ought to be an abstract type? But it allows for some pseudo multiple inheritance
const TotalDataMigration{F<:FinDomFunctor} = DataMigration{F,Dict{Any,Union{}}}
TotalDataMigration(functor)=DataMigration(functor,Dict{Any,Union{}}())
""" Schema-level functor defining a pullback or delta data migration.
"""
const DeltaSchemaMigration{D<:FinCat,C<:FinCat} = AbstractContravariantMigration{<:FinFunctor{D,C}}
#Note TotalDeltaMigration <: DeltaSchemaMigration as well as TotalDataMigration. 
#This only exists for the acset to acset migrate! method which is performance-optimized for 
#the easy Delta case
const TotalDeltaMigration{D<:FinCat,C<:FinCat} = TotalDataMigration{<:FinFunctor{D,C}}

""" Schema-level functor defining a contravariant data migration using conjunctive queries.
"""
const ConjSchemaMigration{D<:FinCat,C<:FinCat} =
  AbstractContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:ConjQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluing queries.
"""
const GlueSchemaMigration{D<:FinCat,C<:FinCat} =
  AbstractContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlueQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluc queries.
"""
const GlucSchemaMigration{D<:FinCat,C<:FinCat} =
  AbstractContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlucQuery{C}}}}

""" Sigma or left pushforward functorial data migration between acsets.

  Given a functor ``F: C → D``, the sigma data migration ``Σ_F`` is a functor from
  ``C``-sets to ``D``-sets that is left adjoint to the delta migration functor
  ``Δ_F`` ([`DeltaMigration`](@ref)). Explicitly, the ``D``-set ``Σ_F(X)`` is
  given on objects ``d ∈ D`` by the formula ``Σ_F(x)(d) = \\mathrm{colim}_{F ↓ d}
  X ∘ π``, where ``π: (F ↓ d) → C`` is the projection.
  
  See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
const SigmaSchemaMigration{F<:FinFunctor} = AbstractCovariantMigration{F}
struct SigmaMigration{F<:FinFunctor} <: SigmaSchemaMigration{F}
  functor::F
end
# Contravariant migration
#########################

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
migrate(Y::ACSet,M::DeltaSchemaMigration) = migrate(FinDomFunctor(Y),M)
migrate(Y::FinDomFunctor,M::DeltaSchemaMigration) = compose(M,Y)
#TODO: write compose

migrate(::Type{T}, X::ACSet, M::TotalDeltaMigration) where T <: ACSet =
  migrate!(T(), X, M)
migrate(::Type{T}, X::ACSet, FOb, FHom) where T <: ACSet =
  migrate!(T(), X, FOb, FHom)

function migrate!(X::StructACSet{S}, Y::ACSet, M::TotalDeltaMigration) where S
  F = functor(M)
  partsX = Dict(c => add_parts!(X, c, nparts(Y, nameof(ob_map(F,c))))
                for c in ob(S))
  for (f,c,d) in homs(S)
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, hom_map(F,f))])
  end
  for (f,c,_) in attrs(S)
    set_subpart!(X, partsX[c], f, subpart(Y, hom_map(F,f)))
  end
  return X
end

function migrate!(X::ACSet, Y::ACSet, FOb, FHom)
  M = TotalDataMigration(FinFunctor(FOb, FHom, FinCat(Presentation(X)), FinCat(Presentation(Y))))
  migrate!(X, Y, M)
end

# Conjunctive migration
#----------------------
#todo: generalize compose for non-total migrations
function migrate(X::FinDomFunctor, M::ConjSchemaMigration;
                 return_limits::Bool=false, tabular::Bool=false)
  F = functor(M)
  tgt_schema = dom(F)
  limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    J = shape(Fc)
    # XXX: Must supply object/morphism types to handle case of empty diagram.
    diagram_types = if c isa AttrTypeExpr
      (TypeSet, SetFunction)
    elseif isempty(J)
      (FinSet{Int}, FinFunction{Int})
    else
      (SetOb, FinDomFunction{Int})
    end
    #
    # XXX: Disable domain check because acsets don't store schema equations.
    lim = limit(force(compose(Fc, X, strict=false), diagram_types...),
                alg=SpecializeLimit(fallback=ToBipartiteLimit()))
    if tabular
      names = (ob_generator_name(J, j) for j in ob_generators(J))
      TabularLimit(lim, names=names)
    else
      lim
    end
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    # XXX: Disable domain check for same reason.
    universal(compose(Ff, X, strict=false), limits[c], limits[d])
  end
  Y = FinDomFunctor(mapvals(ob, limits), funcs, tgt_schema)
  return_limits ? (Y, limits) : Y
end

# Gluing migration
#-----------------

function migrate(X::FinDomFunctor, M::GlueSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  colimits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    diagram_types = c isa AttrTypeExpr ? (TypeSet, SetFunction) :
      (FinSet{Int}, FinFunction{Int})
    colimit(force(compose(Fc, X, strict=false), diagram_types...),
            alg=SpecializeColimit())
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    universal(compose(Ff, X, strict=false), colimits[c], colimits[d])
  end
  FinDomFunctor(mapvals(ob, colimits), funcs, tgt_schema)
end

# Gluc migration
#---------------

function migrate(X::FinDomFunctor, M::GlucSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  colimits_of_limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    Fc_set, limits = migrate(X, diagram(Fc), return_limits=true)
    (colimit(Fc_set, SpecializeColimit()), Fc_set, limits)
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    Fc_colim, Fc_set, Fc_limits = colimits_of_limits[c]
    Fd_colim, Fd_set, Fd_limits = colimits_of_limits[d]
    component_funcs = map(ob_generators(dom(Fc_set))) do j
      j′, Ffⱼ = ob_map(Ff, j)
      universal(compose(Ffⱼ, X, strict=false), Fc_limits[j], Fd_limits[j′])
    end
    Ff_set = DiagramHom{id}(shape_map(Ff), component_funcs, Fc_set, Fd_set)
    universal(Ff_set, Fc_colim, Fd_colim)
  end
  FinDomFunctor(mapvals(ob∘first, colimits_of_limits), funcs, tgt_schema)
end

""" Abstract type for a data migration functor.

This allows the user to have an actual model of the theory of 
functors, once one knows the exact concrete types Dom and Codom
of the relevant acsets. 
"""
abstract type MigrationFunctor{Dom<:ACSet,Codom<:ACSet} <:
  Functor{TypeCat{Dom,ACSetTransformation},TypeCat{Codom,ACSetTransformation}} end

ob_map(F::MigrationFunctor{Dom,Codom}, X) where {Dom,Codom} =
  ob_map(F, Codom, X)

(F::MigrationFunctor)(X::ACSet) = ob_map(F, X)
(F::MigrationFunctor)(α::ACSetTransformation) = hom_map(F, α)
"""
Data migration functor given contravariantly. Stores a contravariant migration.
"""
struct DataMigrationFunctor{Dom,Codom,M<:AbstractContravariantMigration} <: MigrationFunctor{Dom,Codom}
  migration::M
end
migration(F::DataMigrationFunctor) = F.migration
functor(F::DataMigrationFunctor) = functor(migration(F))

DataMigrationFunctor(functor::F, ::Type{Dom}, ::Type{Codom}) where {F,Dom,Codom} =
  DataMigrationFunctor{Dom,Codom,TotalDataMigration{F}}(TotalDataMigration(functor))
DataMigrationFunctor(functor::F, ::Type{Codom}) where {F,Codom} =
  DataMigrationFunctor{ACSet,Codom,TotalDataMigration{F}}(TotalDataMigration(functor))

ob_map(F::DataMigrationFunctor, T::Type, X) = migrate(T, X, migration(F))

const DeltaMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:DeltaSchemaMigration}
const ConjMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:ConjSchemaMigration}
const GlueMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlueSchemaMigration}
const GlucMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlucSchemaMigration}

# Sigma migration
#################
struct SigmaMigrationFunctor{Dom,Codom,M<:SigmaSchemaMigration} <: MigrationFunctor{Dom,Codom}
  migration::M
  dom_constructor
  codom_constructor
  SigmaMigrationFunctor(f::F,d::ACSet,c::ACSet) where F<:FinFunctor = 
    new{typeof(d),typeof(c),SigmaMigration{F}}(SigmaMigration(f),constructor(d),constructor(c))
end 
migration(F::SigmaMigrationFunctor) = F.migration
functor(F::SigmaMigrationFunctor) = functor(migration(F))

SigmaMigrationFunctor(f,::Type{T},c::ACSet) where T<:StructACSet = SigmaMigrationFunctor(f,T(),constructor(c))
SigmaMigrationFunctor(f,d::ACSet,::Type{T}) where T<:StructACSet = SigmaMigrationFunctor(f,d,T())
SigmaMigrationFunctor(f,d::Type{T′},::Type{T}) where {T<:StructACSet, T′<:StructACSet} = SigmaMigrationFunctor(f,d,T())
"""
Create a C-Set for the collage of the functor. Initialize data in the domain 
portion of the collage, then run the chase.
"""
#This should be deprecated in terms of a new migrate function if anybody works on sigma migrations sometime.
#Also, we probably don't want to construct the collage every time we migrate using M, at least it should
#be possible to cache.
function (M::SigmaMigrationFunctor)(d::ACSet; n=100)
  D,CD = M.dom_constructor(), M.codom_constructor()
  S = acset_schema(d)
  col, col_pres = collage(functor(M))
  i1,i2 = legs(col)
  # Initialize collage C-Set with data from `d`
  atypes = Dict{Symbol,Type}()
  for (k,v) in datatypes(D)  atypes[Symbol(ob_map(i1,k))] = v end
  for (k,v) in datatypes(CD) atypes[Symbol(ob_map(i2,k))] = v end
  col_type = crel_type(presentation(apex(col)); types=atypes, name="Sigma")()
  for o in ob(S)
    add_parts!(col_type, Symbol(ob_map(i1,o)), nparts(d,o))
  end
  for h in homs(S; just_names=true)
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
  S2 = acset_schema(res)
  for o in types(S2)
    add_parts!(res, o, nparts(rel_res, Symbol(ob_map(i2,o))))
  end 
  for h in arrows(S2;just_names=true)
    hsrc, htgt = add_srctgt(hom_map(i2,h))
    for (domval, codomval) in zip(rel_res[hsrc], rel_res[htgt])
      res[domval,h] = codomval
    end
  end
  return res
end 


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
function representable(T, C::Presentation{ThSchema}, ob::Symbol)
  C₀ = Presentation{Symbol}(FreeSchema)
  add_generator!(C₀, C[ob])
  X = AnonACSet(C₀); add_part!(X, ob)
  F = FinFunctor(Dict(ob => ob), Dict(), C₀, C)
  ΣF = SigmaMigrationFunctor(F, X, T)
  return ΣF(X)
end

"""
ACSet types do not store info about equations, so this info is lost when we try
to recover the presentation from the datatype. Thus, this method for 
`representable` should only be used for free schemas
""" 
representable(::Type{T}, ob::Symbol) where T <: StructACSet =
  representable(T, Presentation(T), ob)

""" Yoneda embedding of category C in category of C-sets.

Because Catlab privileges copresheaves (C-sets) over presheaves, this is the
*contravariant* Yoneda embedding, i.e., the embedding C^op → C-Set.

If representables have already been computed (which can be expensive) they can
be provided via the `cache` keyword argument.

Input `cons` is a constructor for the ACSet

Returns a `FinDomFunctor` with domain `op(C)`.
"""
function yoneda(cons, C::Presentation{ThSchema}; cache=nothing)
  cache = isnothing(cache) ? Dict() : cache
  y_ob = Dict(map(nameof.(generators(C, :Ob))) do c 
    @debug "Computing representable $c"
    c => haskey(cache, c) ? cache[c] : representable(cons, C, c)
  end)
  y_ob = merge(y_ob, Dict(map(nameof.(generators(C,:AttrType))) do c 
    rep = cons()
    add_part!(rep, c)
    c => rep
  end))
  y_hom = Dict(Iterators.map(generators(C, :Hom) ∪ generators(C, :Attr)) do f
    c, d = nameof.([dom(f), codom(f)])
    yc, yd = y_ob[c], y_ob[d]
    initial = Dict(d => Dict(1 => yc[1,f]))
    f => homomorphism(yd, yc, initial=initial) # Unique homomorphism.
  end)
  FinDomFunctor(y_ob, y_hom, op(FinCat(C)))
end
yoneda(::Type{T}; kw...) where T <: StructACSet = yoneda(T, Presentation(T); kw...)
yoneda(X::DynamicACSet; kw...) = yoneda(constructor(X), Presentation(X.schema); kw...)

""" Interpret conjunctive data migration as a colimit of representables.

Given a conjunctive data migration (a functor `J → Diag{op}(C)`) and the Yoneda
embedding for `C` (a functor `op(C) → C-Set` computed via [`yoneda`](@ref)),
take colimits of representables to construct a `op(J)`-shaped diagram of C-sets.

Since every C-set is a colimit of representables, this is a generic way of
constructing diagrams of C-sets.
"""
function colimit_representables(M::DeltaSchemaMigration, y)
  compose(op(functor(M)), y)
end
function colimit_representables(M::ConjSchemaMigration, y)
  F = functor(M)
  C = dom(F)
  ACS = constructor(ob_map(y,first(ob_generators(dom(y)))))
  colimits = make_map(ob_generators(C)) do c
    Fc = ob_map(F, c) # e.g. I
    clim_diag = deepcopy(diagram(compose(op(Fc), y)))
    # modify the diagram we take a colimit of to concretize some vars
    params = Fc isa SimpleDiagram ? Dict() : Fc.params
    G, om, hm = [f(clim_diag) for f in [graph ∘ dom, ob_map, hom_map]]
    for (i,val) in collect(params)
      v = add_vertex!(G; vname=Symbol("param$i"))
      add_edge!(G, i, v; ename=Symbol("param$i"))
      at = nameof(ob_map(Fc, i)) # attribute type name 
      h = only(homomorphisms(ob_map(clim_diag,i), ACS(); initial=Dict(at=>[val])))
      push!(om, ACS())
      push!(hm, h)
    end
    updated_diagram = FinDomFunctor(om, hm, FinCat(G), codom(clim_diag))
    colimit(updated_diagram) # take colimit
  end
  homs = make_map(hom_generators(C)) do f
    Ff, c, d = hom_map(F, f), dom(C, f), codom(C, f)
    universal(compose(op(Ff), y), colimits[d], colimits[c])
  end
  FinDomFunctor(mapvals(ob, colimits), homs, op(C))
end

# Schema translation
####################

# FIXME: This function does not belong here.

"""   FreeDiagram(pres::Presentation{FreeSchema, Symbol})

Returns a `FreeDiagram` whose objects are the generating objects of `pres` and 
whose homs are the generating homs of `pres`.
"""
function FreeDiagrams.FreeDiagram(pres::Presentation{ThSchema, Symbol})
  obs = Array{FreeSchema.Ob}(generators(pres, :Ob))
  homs = Array{FreeSchema.Hom}(generators(pres, :Hom))
  doms = map(h -> generator_index(pres, nameof(dom(h))), homs)
  codoms = map(h -> generator_index(pres, nameof(codom(h))), homs)
  return FreeDiagram(obs, collect(zip(homs, doms, codoms)))
end

end


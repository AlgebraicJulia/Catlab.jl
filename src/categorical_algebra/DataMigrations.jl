""" Functorial data migration for attributed C-sets.
"""
module DataMigrations
export DataMigration, SigmaMigration, DeltaMigration, migrate, migrate!,
  representable, yoneda, colimit_representables, subobject_classifier, 
  internal_hom, SigmaMigrationFunctor, DeltaMigrationFunctor, 
  DataMigrationFunctor, functor

using ACSets
using ACSets.DenseACSets: constructor, datatypes
using ...GATs
using ...Theories: ob, hom, dom, codom, attr, AttrTypeExpr, ⋅
using ..Categories, ..FinCats, ..Limits, ..Diagrams, ..FinSets, ..CSets, ..HomSearch
using ...Graphs, ..FreeDiagrams
import ..Categories: ob_map, hom_map
import ...GATs: functor
using ..FinCats: make_map, mapvals, presentation_key
using ..Diagrams
import ..FinCats: FinCatPresentation
using ..Chase: collage, crel_type, pres_to_eds, add_srctgt, chase
using ..FinSets: VarSet
using MLStyle: @match

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
abstract type ContravariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end
abstract type CovariantMigration{F<:FinDomFunctor} <: AbstractDataMigration{F} end

"""
A contravariant data migration whose functor ``F`` may not be fully defined. Instead,
the migration ``F⋅X`` for an acset ``X`` can only be constructed once we have access
to ``X``'s attribute types. The dictionary of parameters contains anonymous 
functions acting on ``X``'s attributes using Julia functions defined on 
these attribute types.
"""
#The same, except for the supertype and the variance parameter T, as a QueryDiagram in older code.
#(Instead, `C` itself is probably a category of queries, which thus contain the information of T further down.)
struct DataMigration{F<:FinDomFunctor,Params<:AbstractDict} <: ContravariantMigration{F}
  functor::F
  params::Params
end
DataMigration(F::FinDomFunctor) = DataMigration(F,Dict{Any,Union{}}())
""" Schema-level functor defining a pullback or delta data migration.
"""
const DeltaSchemaMigration{D<:FinCat,C<:FinCat} = ContravariantMigration{<:FinFunctor{D,C}}
#This only exists for the acset to acset migrate! method which is performance-optimized for 
#the easy Delta case
const DeltaMigration{D<:FinCat,C<:FinCat} = DataMigration{<:FinFunctor{D,C},<:AbstractDict{<:Any,Union{}}}

""" Schema-level functor defining a contravariant data migration using conjunctive queries.
"""
const ConjSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:ConjQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluing queries.
"""
const GlueSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlueQuery{C}}}}

""" Schema-level functor defining a contravariant data migration using gluc queries.
"""
const GlucSchemaMigration{D<:FinCat,C<:FinCat} =
  ContravariantMigration{<:FinDomFunctor{D,<:TypeCat{<:GlucQuery{C}}}}

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
function migrate(X::FinDomFunctor,M::DeltaSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  src_schema = get_src_schema(F)
  obs = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F,c)
    ob_map(X,Fc)
  end
  hg = hom_generators(src_schema)
  homnames = map(presentation_key,hg)
  homfuns = map(x->hom_map(X,x),homnames)
  params = M.params
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    if Ff isa GATExpr{:zeromap} #this is ugly but mo fincatgraphs mo problems
      domain = obs[c]
      codomain = obs[d]
      FinDomFunction(params[nameof(f)](homfuns...),domain,codomain)
    else 
      hom_map(X,Ff)
    end
  end
  FinDomFunctor(
      obs,
      funcs,
      dom(F),
      codom(X)
    )
end

migrate(::Type{T}, X::ACSet, M::DeltaMigration) where T <: ACSet =
  migrate!(T(), X, M)
migrate(::Type{T}, X::ACSet, FOb, FHom) where T <: ACSet =
  migrate!(T(), X, FOb, FHom)

function migrate!(X::StructACSet{S}, Y::ACSet, M::DeltaMigration) where S
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
  M = DataMigration(FinFunctor(FOb, FHom, FinCat(Presentation(X)), FinCat(Presentation(Y))))
  migrate!(X, Y, M)
end

"""
Get the names of the morphisms in a schema given either
by a NamedGraph or by a presentation.
"""
get_homnames(S::FinCatGraph) = collect(subpart(graph(S),:,:ename))
get_homnames(S::FinCatPresentation) = map(presentation_key,hom_generators(S))
get_homnames(S::FinCat) = Symbol[]

"""
Get the source schema of a data migration functor, recursing in the case
that the proximate codomain is a diagram category.
"""
function get_src_schema(F::Functor)
  #the below is quite unhappy but I couldn't figure out how to dispatch
    #on the parameters of the diagram object type, too much invariance.
  if codom(F) isa TypeCat{<:Diagram}  
    obs = collect(keys(F.ob_map))
    length(obs) > 0 || return FinCat(0)
    get_src_schema(diagram(ob_map(F,obs[1])))
  else 
    codom(F)
  end
end

#=
#Arbitrary migration
function migrate(X::FinDomFunctor, M::ContravariantDataMigration;
  return_limits::Bool=false, tabular::Bool=false,colimit::Bool=false)
  F = functor(M)
  tgt_schema = dom(F)
  homnames = get_homnames(X, tgt_schema)
  homfuns = map(x -> hom_map(X, x), homnames)
  params = M.params
  lims_or_colims = make_map(ob_generators(tgt_schema)) do c
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
    limit_or_colimit = colimit ? colimit : limit
    alg = colimit ? SpecializeColimit() : SpecializeLimit(fallback=ToBipartiteLimit())
    lim_or_colim = limit_or_colimit(force(compose(Fc, X, strict=false), diagram_types...),alg=alg)
    if tabular
      names = (ob_generator_name(J, j) for j in ob_generators(J))
      TabularLimit(lim_or_colim, names=names)
    else
      lim_or_colim
    end
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    f_params = haskey(params, f) ? map(x -> x(homfuns...), params[f]) : []
    # XXX: Disable domain check for same reason.
    # Hand the Julia function form of the not-yet-defined components to compose
    universal(compose(Ff, X, strict=false, params=f_params), limits[c], limits[d])
  end
  Y = FinDomFunctor(mapvals(ob, limits), funcs, tgt_schema)
  return_limits ? (Y, limits) : Y
end
=#
#=
function codom_r(F::Functor{Dom,Codom}) where {Dom,Codom}
  @match Codom begin
    a::Type{TypeCat{T,S}} where {T,S}=> codom_r(T)
    a::Type{Diagram{T,C,F}} where {T,C,F} => codom_r(C)
    a::Type{QueryDiagram{T,C,F,P}} where {T,C,F,P} => codom_r(C)
    a::Type{<:FinCat} => C
    _ => "you done it now"
  end
end
=#
# Conjunctive migration
#----------------------
function migrate(X::FinDomFunctor, M::ConjSchemaMigration;
                 return_limits::Bool=false, tabular::Bool=false)
  F = functor(M)
  tgt_schema = dom(F)
  homnames = get_homnames(get_src_schema(F))
  homfuns = map(x->hom_map(X,x),homnames)
  params = M.params
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
    # Make sure the diagram to be limited is a FinCat{<:Int}.
    # XXX: Disable domain check because acsets don't store schema equations.
    k = dom_to_graph(diagram(force(compose(Fc, X, strict=false), diagram_types...)))
    lim = limit(k,SpecializeLimit(fallback=ToBipartiteLimit()))
    if tabular
      names = (ob_generator_name(J, j) for j in ob_generators(J))
      TabularLimit(lim, names=names)
    else
      lim
    end
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    #Not sure whether params[nameof(f)] might ever
    #need to have multiple entries.
    f_params = haskey(params,nameof(f)) ? Dict(nameof(codom(f)) => params[nameof(f)](homfuns...)) : Dict()
    # XXX: Disable domain check for same reason.
    # Hand the Julia function form of the not-yet-defined components to compose
    universal(compose(Ff, X, strict=false,params=f_params), limits[c], limits[d])
  end
  Y = FinDomFunctor(mapvals(ob, limits), funcs, tgt_schema)
  return_limits ? (Y, limits) : Y
end

# Gluing migration
#-----------------

function migrate(X::FinDomFunctor, M::GlueSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  homnames = get_homnames(get_src_schema(F))
  homfuns = map(x->hom_map(X,x),homnames)
  params = M.params
  colimits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    diagram_types = c isa AttrTypeExpr ? (TypeSet, SetFunction) :
      (FinSet{Int}, FinFunction{Int})
    k = dom_to_graph(diagram(force(compose(Fc, X, strict=false), diagram_types...)))
    colimit(k,SpecializeColimit())
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    #Get a single anonymous function, if there's one needed and 
    #the domain of Ff's shape map is a singleton, or else get a dict
    #of them if the domain is a non-singleton and there are any.
    f_params = haskey(params,f) ? map(x->x(homfuns...),params[f]) : 
                isempty(get_params(Ff)) ? [] : mapvals(x->x(homfuns...),get_params(Ff))
    universal(compose(Ff, X, strict=false,params=f_params), colimits[c], colimits[d])
  end
  FinDomFunctor(mapvals(ob, colimits), funcs, tgt_schema)
end

# Gluc migration
#---------------

function migrate(X::FinDomFunctor, M::GlucSchemaMigration)
  F = functor(M)
  tgt_schema = dom(F)
  homnames = get_homnames(get_src_schema(F))
  homfuns = map(x->hom_map(X,x),homnames)
  colimits_of_limits = make_map(ob_generators(tgt_schema)) do c
    Fc = ob_map(F, c)
    m = Fc isa QueryDiagram ? DataMigration(diagram(Fc),Fc.params) : DataMigration(diagram(Fc))
    Fc_set, limits = migrate(X, m, return_limits=true)
    (colimit(dom_to_graph(Fc_set), SpecializeColimit()), Fc_set, limits)
  end
  funcs = make_map(hom_generators(tgt_schema)) do f
    Ff, c, d = hom_map(F, f), dom(tgt_schema, f), codom(tgt_schema, f)
    Fc_colim, Fc_set, Fc_limits = colimits_of_limits[c]
    Fd_colim, Fd_set, Fd_limits = colimits_of_limits[d]
    Ff_params = Ff isa DiagramHom ? get_params(Ff) : Dict{Int,Int}()
    component_funcs = make_map(ob_generators(dom(Fc_set))) do j
      j′, Ffⱼ = ob_map(Ff, j)
      Ffⱼ_params = Ffⱼ isa DiagramHom ? 
        haskey(Ff_params,nameof(j)) ? 
          Dict(only(keys(components(diagram_map(Ffⱼ))))=>Ff_params[nameof(j)](homfuns...)) :
          mapvals(x->x(homfuns...),get_params(Ffⱼ)) : Dict{Int,Int}()
      universal(compose(Ffⱼ, X, strict=false,params = Ffⱼ_params), 
                Fc_limits[j], Fd_limits[j′])
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
functor(F::DataMigrationFunctor) = functor(migration(F))

DataMigrationFunctor(migration::ContravariantMigration{F}) where {F<:Functor{Dom,Codom} where {Dom,Codom}} = DataMigrationFunctor{Dom,Codom,M}(migration)
DataMigrationFunctor(functor::F, ::Type{Dom}, ::Type{Codom}) where {F,Dom,Codom} =
  DataMigrationFunctor{Dom,Codom,DataMigration{F,Dict{Any,Union{}}}}(DataMigration(functor))
DataMigrationFunctor(functor::F, ::Type{Codom}) where {F,Codom} =
  DataMigrationFunctor{ACSet,Codom,DataMigration{F,Dict{Any,Union{}}}}(DataMigration(functor))

ob_map(F::DataMigrationFunctor, T::Type, X) = migrate(T, X, migration(F))

const DeltaMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:DeltaSchemaMigration}
const ConjMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:ConjSchemaMigration}
const GlueMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlueSchemaMigration}
const GlucMigrationFunctor{Dom,Codom} = DataMigrationFunctor{Dom,Codom,<:GlucSchemaMigration}

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

SigmaMigrationFunctor(f,::Type{T},c::ACSet) where T<:StructACSet = SigmaMigrationFunctor(f,T(),constructor(c))
SigmaMigrationFunctor(f,d::ACSet,::Type{T}) where T<:StructACSet = SigmaMigrationFunctor(f,d,T())
SigmaMigrationFunctor(f,d::Type{T′},::Type{T}) where {T<:StructACSet, T′<:StructACSet} = SigmaMigrationFunctor(f,d,T())

"""
Create a C-Set for the collage of the functor. Initialize data in the domain 
portion of the collage, then run the chase.

When `return_unit` is true, returns the diagram morphism given by the unit of
the adjunction between Σ and Δ migration functors.
"""
#This should be deprecated in terms of a new migrate function if anybody works on sigma migrations sometime.
#Also, we probably don't want to construct the collage every time we migrate using M, at least it should
#be possible to cache.
function (M::SigmaMigrationFunctor)(d::ACSet; n=100, return_unit::Bool=false)
  D,CD = M.dom_constructor(), M.codom_constructor()
  F = functor(M)
  S = acset_schema(d)
  #ask the collage to represent a transformation that's natural
  #only on the non-attrtype objects of the domain
  obs = map(x->Ob(FreeSchema.Ob,x),S.obs)
  col, col_pres = collage(functor(M),objects=obs)
  i1,i2 = legs(col)
  # Initialize collage C-Set with data from `d`
  atypes = Dict{Symbol,Type}()
  for (k,v) in datatypes(D)  atypes[Symbol(ob_map(i1,k))] = v end
  for (k,v) in datatypes(CD) atypes[Symbol(ob_map(i2,k))] = v end
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
  #Go back and make sure attributes that ought to have
  #specific values because of d do have those values.
  for (k,kdom,kcod) in attrs(S)
    f = hom_map(F,k)
    #split f into its hom part and its attr part
    f1,f2 = split_r(f)
    #Need f1 on the collage for rel_res but f2 
    #on the target schema
    f1 = hom_map(i2,f1)
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

  # Return result as DiagramHom{id}.
  diagram_map = Dict(map(types(S)) do o
    s, t= add_srctgt("α_$o")
    m = last.(sort(collect(zip([rel_res[x] for x in [s,t]]...))))
    ff = o ∈ ob(S) ? FinFunction : VarFunction{attrtype_type(D,o)}
    o => ff(m, nparts(rel_res, nameof(ob_map(functor(M)⋅i2,o))))
  end)
  ddom = FinDomFunctor(d; equations=equations(dom(functor(M))))
  dcodom = FinDomFunctor(res; equations=equations(codom(functor(M))))
  DiagramHom{id}(functor(M), diagram_map, ddom, dcodom)
end

"""
Split an n-fold composite (n may be 1) 
Hom or Attr into its left n-1 and rightmost 1 components
"""
split_r(f) = head(f) == :compose ?
  (compose(args(f)[1:end-1]),last(f)) : (id(dom(f)),f)

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
function representable(T, C::Presentation{ThSchema}, ob::Symbol;
                       return_unit_id::Bool=false)
  C₀ = Presentation{Symbol}(FreeSchema)
  add_generator!(C₀, C[ob])
  X = AnonACSet(C₀); add_part!(X, ob)
  F = FinFunctor(Dict(ob => ob), Dict(), C₀, C)
  ΣF = SigmaMigrationFunctor(F, X, T)
  if return_unit_id
    η = ΣF(X; return_unit=true)
    (ACSet(diagram(codom(η))), only(collect(diagram_map(η)[ob])))
  else
    ΣF(X)
  end
end

"""
ACSet types do not store info about equations, so this info is lost when we try
to recover the presentation from the datatype. Thus, this method for 
`representable` should only be used for free schemas
""" 
representable(::Type{T}, ob::Symbol; kw...) where T <: StructACSet =
  representable(T, Presentation(T), ob; kw...)


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
function subobject_classifier(T::Type, S::Presentation{ThSchema}; kw...)
  isempty(generators(S, :AttrType)) ||
    error("Cannot compute Ω for schema with attributes")
  y = yoneda(T, S; kw...)
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
function internal_hom(G::T, F::T, S::Presentation{ThSchema}; kw...) where T<:ACSet
  y = yoneda(T, S; kw...)
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
function yoneda(cons, C::Presentation{ThSchema};
                cache::AbstractDict=Dict{Symbol,Any}())
  # Compute any representables that have not already been computed.
  for c in nameof.(generators(C, :Ob))
    haskey(cache, c) && continue
    cache[c] = representable(cons, C, c, return_unit_id=true)
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
    P, om, hm = [f(clim_diag) for f in [presentation ∘ dom, ob_map, hom_map]]
    s = P.syntax
    #XX:Not sure whether below is correctly modified from graph to presentation
    for (i,val) in collect(params)
      v = add_generator!(P,s.Ob(s.Ob,Symbol("param$i")))
      f = add_generator!(P,Hom(Symbol("param$i"),i,v))
      at = nameof(ob_map(Fc, i)) # attribute type name 
      h = only(homomorphisms(ob_map(clim_diag,i), ACS(); initial=Dict(at=>[val])))
      om[v] = ACS()
      hm[f] = h
    end
    updated_diagram = FinDomFunctor(om, hm, FinCat(P), codom(clim_diag))
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


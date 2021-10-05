""" Functorial data migration for C-sets.
"""
module DataMigration
export Delta, Sigma, migrate!

using ...Present, ...Theories
using ...Theories: SchemaDesc, ob, hom, dom, codom, attr, adom
using ..FinSets, ..CSets, ..Limits, ...Graphs, ..FreeDiagrams
using ..Categories, ..FinCats
import ...Present: Presentation
import ...CategoricalAlgebra.FreeDiagrams: FreeDiagram

const ACSetCat = TypeCat{ACSet,ACSetTransformation}

""" Abstract type for functor that migrates data from one ACSet to another.
"""
abstract type MigrationFunctor <: Functor{ACSetCat,ACSetCat} end

codom_type(F::MigrationFunctor) = F.codom_type

(F::MigrationFunctor)(X::ACSet) = F(codom_type(F)(), X)

# Delta migration
#################

""" Pullback functorial data migration from one ACSet to another.

Note that this operation is contravariant: the data is transferred from `Y` to
`X` but the functor, represented by two dictionaries, maps the schema for `X`
to the schema for `Y`.

When the functor is the identity, this operation is equivalent to
[`copy_parts!`](@ref).
"""
struct DeltaMigration <: MigrationFunctor
  F::FinFunctor # on the schemas
  codom_type::Type
end

"""   Delta(F::FinFunctor)

Given a functor ``F: \\mathcal{C} \\to \\mathcal{D}`` produces a `MigrationFunctor`
which maps a ``\\mathcal{D}``-set ``X`` to the ``\\mathcal{C}``-set 
``\\Delta_F(X) := X \\circ F``.

See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
Delta(F::FinFunctor, codom) = DeltaMigration(F, codom)
Delta(F::FinFunctor, dom, codom) = DeltaMigration(F, codom)

(ΔF::DeltaMigration)(X::ACSet, Y::ACSet) = migrate!(X, Y, ΔF.F)

"""   migrate!(X::ACSet, Y::ACSet, FOb, FHom)

Migrates the data from `Y` to `X` via the pullback data migration induced by the
functor defined on objects by `FOb` and on morphisms by `FHom`.
"""
function migrate!(X::StructACSet{S}, Y::ACSet, F::FinFunctor) where S
  partsX = Dict(c => add_parts!(X, c, nparts(Y, nameof(ob_map(F,c))))
                for c in ob(S))

  for (f,c,d) in zip(hom(S), dom(S), codom(S))
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, hom_map(F,f))])
  end
  for (f,c) in zip(attr(S), adom(S))
    set_subpart!(X, partsX[c], f, subpart(Y, hom_map(F,f)))
  end

  return X
end

function migrate!(X::ACSet, Y::ACSet, FOb, FHom)
  F = FinFunctor(FOb, FHom, FinCat(Presentation(X)), FinCat(Presentation(Y)))
  migrate!(X, Y, F)
end

function (::Type{T})(Y::ACSet, FOb::AbstractDict, FHom::AbstractDict) where T <: ACSet
  X = T()
  migrate!(X, Y, FOb, FHom)
end

function (::Type{T})(Y::ACSet, F::FinFunctor) where T <: ACSet
  X = T()
  migrate!(X, Y, F)
end

# Sigma migration
#################

""" Left pushforward functorial data migration from one ACSet to another.
"""
struct SigmaMigration{CC} <: MigrationFunctor
  F::FinFunctor # on the schemas
  codom_type::Type
  comma_cats::CC

  function SigmaMigration(F::FinFunctor, codom_type)
    cc = get_comma_cats(F)
    new{typeof(cc)}(F, codom_type, cc)
  end
end

"""   Sigma(F::FinFunctor)

Given a functor ``F: \\mathcal{C} \\to \\mathcal{D}`` produces a `MigrationFunctor`
which maps a ``\\mathcal{C}``-set ``X`` to the ``\\mathcal{D}``-set ``\\Sigma_F(X)``.
``\\Sigma_F`` is left-adjoint to ``\\Delta_F``. 

For ``d \\in \\mathsf{ob}\\mathcal{D}``, 
``\\Sigma_F(X)(d) := \\mathsf{colim}_{F \\downarrow d} X \\circ \\pi`` where 
``\\pi: F\\downarrow d \\to \\mathcal{C}`` is the projection. 

See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
Sigma(F::FinFunctor, codom) = SigmaMigration(F, codom)
Sigma(F::FinFunctor, dom, codom) = SigmaMigration(F, codom)

function (ΣF::SigmaMigration)(Y::ACSet, X::ACSet)
  comma_cats = ΣF.comma_cats
  diagramD = FreeDiagram(presentation(codom(ΣF.F)))

  # define Y on objects by taking colimits
  colimX = map(parts(diagramD, :V)) do i
    F∇d = ob(comma_cats, i)
    Xobs = map(ob(F∇d)) do (c,_)
      FinSet{Int,Int}(nparts(X, nameof(c)))
    end
    Xhoms = map(parts(F∇d, :E)) do g
      FinFunction(X[nameof(hom(F∇d, g))], Xobs[src(F∇d, g)], Xobs[tgt(F∇d, g)])
    end
    colimit(FreeDiagram(Xobs, collect(zip(Xhoms, src(F∇d), tgt(F∇d)))))
  end

  for d in parts(diagramD, :V)
    add_parts!(Y, nameof(ob(diagramD, d)), length(apex(colimX[d])))
  end
  
  # Define Y on morphisms by the universal property
  for g in parts(diagramD, :E)
    if nparts(Y, nameof(dom(hom(diagramD, g)))) == 0
      continue
    end
    set_subpart!(Y, nameof(hom(diagramD, g)),
      collect(universal(colimX[src(diagramD, g)],
        Multicospan(legs(colimX[tgt(diagramD, g)])[collect(hom(comma_cats, g)[:V])])
      )))
  end
  return Y
end


""" add_hom!(d::FreeDiagram{Ob, Hom}, src_ob::Ob, tgt_ob::Ob, hom::Hom)

Adds a hom to `d` from the vertex with object `src_ob` to the vertex with object `tgt_ob`.
"""
function add_hom!(d::FreeDiagram, src_ob, tgt_ob, hom) 
  src_idx = first(incident(d, src_ob, :ob))
  tgt_idx = first(incident(d, tgt_ob, :ob))
  return add_edge!(d, src_idx, tgt_idx, hom = hom)
end

"""   comma_cats(diagramD::FreeDiagram{FreeSchema.Ob, FreeSchema.Hom}, FOb, FHom)

Given a free category ``\\mathcal{D}`` with no cycles and 
a functor represented by the pair `(FOb, FHom)`, returns a diagram 
``\\mathcal{D} \\to \\mathsf{Cat}`` which on objects takes ``d \\in \\mathcal{D}`` to the 
comma category ``F \\downarrow d``.
"""
function get_comma_cats(F::FinFunctor)
  diagramD = FreeDiagram(presentation(codom(F)))
  FObInv = y -> filter(x -> ob_map(F,x) == y, ob_generators(dom(F)))
  FHomInv = g -> filter(f -> hom_map(F,f) == g, hom_generators(dom(F)))
  comma_cats = FreeDiagram{FreeDiagram, ACSetTransformation}()
  add_vertices!(comma_cats,
    nparts(diagramD, :V), 
    ob = map(parts(diagramD, :V)) do _
      FreeDiagram{Pair{FreeSchema.Ob, FreeSchema.Hom}, FreeSchema.Hom}() 
    end
  )

  for d in topological_sort(diagramD)
    F∇d = ob(comma_cats, d)
    id_d = id(ob(diagramD, d))

    # If FOb[c] = d, add an objects (c, id(d)) to F∇d
    preimage_d = FObInv(ob(diagramD, d)) 
    id_obs = add_vertices!(F∇d, length(preimage_d), ob = map(c->c=>id_d, preimage_d))
    
    # if FHom[h] = id(d), add a hom h: (dom(h), id(d)) -> (codom(h), id(d)) to F∇d 
    id_homs = map(FHomInv(id_d)) do h
      add_hom!(F∇d, dom(h) => id_d, codom(h) => id_d, h)
    end

    # for g: d' -> d in D (note that F∇d' must have already been constructed)
    #     populate F∇d with obs and homs coming from F∇d′
    for g in incident(diagramD, d, :tgt)
      d′ = src(diagramD, g)
      F∇g = comma_cat_hom!(F∇d, ob(comma_cats, d′), id_d, hom(diagramD, g), FHomInv)
      add_edge!(comma_cats, d′, d, hom=F∇g)      
    end 
  end

  return comma_cats
end

function comma_cat_hom!(F∇d, F∇d′, id_d, g, FHomInv)
  # for (c,f) in F∇d' add ob (c, compose(f,g)) to F∇d
  vs = add_vertices!(F∇d, nparts(F∇d′, :V), ob = map(ob(F∇d′)) do (c,f)
    c => compose(f, g)                
  end)

  # for h: (c, f) -> (c', f') in diagram_d', add hom h to F∇d    
  es = add_edges!(F∇d, vs[src(F∇d′)], vs[tgt(F∇d′)], hom = hom(F∇d′))

  # for every (c,f) in the recently added objects. If FHom[h] == f, then add the hom 
  #       h: (c,f) -> (codom(h), idv)
  # relies on D being free
  for (c, f) in ob(F∇d, vs)
    for h in FHomInv(f)
      dom(h) == c && add_hom!(F∇d, c => f, codom(h) => id_d, h)
    end
  end

  # return the inclusion from F∇d′ to F∇d 
  return ACSetTransformation((V = collect(vs), E = collect(es)), F∇d′, F∇d)
end

### Translate between ACSets, Presentations, and FreeDiagrams
#############################################################

# FIXME: These functions do not belong here.

""" Get the Schema from an ACSet
"""
function Presentation(::StructACSet{S}) where S
  return Presentation(S)
end

"""   FreeDiagram(pres::Presentation{FreeSchema, Symbol})

Returns a `FreeDiagram` whose objects are the generating objects of `pres` and 
whose homs are the generating homs of `pres`.
"""
function FreeDiagram(pres::Presentation{Schema, Symbol}) where Schema
  obs = Array{FreeSchema.Ob}(generators(pres, :Ob))
  homs = Array{FreeSchema.Hom}(generators(pres, :Hom))
  doms = map(h -> generator_index(pres, nameof(dom(h))), homs)
  codoms = map(h -> generator_index(pres, nameof(codom(h))), homs)
  return FreeDiagram(obs, collect(zip(homs, doms, codoms)))
end

end

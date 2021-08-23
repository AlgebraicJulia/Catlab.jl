""" Data Migration functors
"""
module DataMigration
export Functor, Delta, Sigma, migrate!, chase

using ...Present, ...Theories
using ...Theories: SchemaDesc, ob, hom, dom, codom, attr
using ..FinSets, ..CSets, ..Limits, ...Graphs, ..FreeDiagrams
using ...CSetDataStructures: struct_acset
using DataStructures

import ...CategoricalAlgebra.FreeDiagrams: FreeDiagram
import ...Present: Presentation
import ...Theories: dom, codom, Ob, Hom


""" Abstract type for a functor.
"""
abstract type AbstractFunctor end

"""   Functor

A functor ``F: \\mathcal{C} \\to \\mathcal{D}`` consists of a map of objects and a
map of homomorphisms from a domain category ``\\mathcal{C}``  to a codomain
category ``\\mathcal{D}``.
"""
struct Functor{O,H,C,D} <: AbstractFunctor
  FOb::O
  FHom::H
  dom::C
  codom::D
end

# interface for abstract functor
dom(F::Functor) = F.dom
codom(F::Functor) = F.codom
Ob(F::Functor) = F.FOb
Hom(F::Functor) = F.FHom

# To construct a functor where FOb and FHom are keyed by the symbols of
# the domain and codomain presentations. Turn them into a dictionaries
# whose keys and values are homs.
function Functor(FOb::Dict{Symbol, Symbol}, FHom::Dict{Symbol, H},
                 dom::Presentation, codom::Presentation) where H
  Functor(
    Dict(dom[c_name] => codom[Fc_name] for (c_name, Fc_name) in FOb),
    Dict(dom[f_name] => get_hom(codom, Ff_name) for (f_name, Ff_name) in FHom),
    dom, codom
  )
end

get_hom(presY::Presentation, Ff::FreeSchema.Hom) = Ff
get_hom(presY::Presentation, Ff::Symbol) = presY[Ff]
get_hom(presY::Presentation, Ff::Array) =
  reduce(compose, map(h -> get_hom(presY, h), Ff))


""" Abstract type for migration functor which migrates data from one ACSet to another
"""
abstract type MigrationFunctor <: AbstractFunctor end

(F::MigrationFunctor)(X::ACSet) = F(codom(F)(),X)

dom(MF::MigrationFunctor) = MF.dom
codom(MF::MigrationFunctor) = MF.codom

#### Delta Migration
###################

""" Pullback functorial data migration from one ACSet to another.

Note that this operation is contravariant: the data is transferred from `Y` to
`X` but the functor, represented by two dictionaries, maps the schema for `X`
to the schema for `Y`.

When the functor is the identity, this function is equivalent to
[`copy_parts!`](@ref).
"""
struct DeltaMigration{D,C} <: MigrationFunctor
  F::Functor # on the schemas
  dom::D
  codom::C
end


"""   Delta(F::Functor)

Given a functor ``F: \\mathcal{C} \\to \\mathcal{D}`` produces a `MigrationFunctor`
which maps a ``\\mathcal{D}``-set ``X`` to the ``\\mathcal{C}``-set
``\\Delta_F(X) := X \\circ F``.

See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
Delta(F::Functor, dom, codom) = DeltaMigration(F, dom, codom)

function (ΔF::DeltaMigration)(X::StructACSet{S}, Y::ACSet) where {S}
  FOb = Ob(ΔF.F)
  FHom = Hom(ΔF.F)

  partsX = Dict(map(ob(S)) do c_name
    c = dom(ΔF.F)[c_name]
    c => add_parts!(X, c_name, nparts(Y, nameof(FOb[c])))
  end)

  for (f, Ff) in collect(FHom)
    doms = partsX[dom(f)]
    subpt = f isa FreeSchema.Hom ? partsX[codom(f)][subpart(Y, Ff)] : subpart(Y, Ff)
    set_subpart!(X, doms, nameof(f), subpt)
  end

  return X
end


"""   migrate!(X::ACSet, Y::ACSet, FOb, FHom)

Migrates the data from `Y` to `X` via the pullback
data migration induced by the functor defined on objects by `FOb` and
on morphisms by `FHom`.
"""
migrate!(X::ACSet, Y::ACSet, F::Functor) = Delta(F, typeof(Y), typeof(X))(X,Y)

migrate!(X::ACSet, Y::ACSet, FOb, FHom) =
  migrate!(X,Y, Functor(FOb, FHom, Presentation(X), Presentation(Y)))

function (::Type{T})(Y::ACSet, FOb::AbstractDict, FHom::AbstractDict) where T <: ACSet
  X = T()
  migrate!(X, Y, FOb, FHom)
end

function (::Type{T})(Y::ACSet, F::Functor) where T <: ACSet
  X = T()
  migrate!(X, Y, F)
end


### SigmaMigration
###################
""" Left pushforward functorial data migration from one ACSet to another.
"""
struct SigmaMigration{D, C, CC} <: MigrationFunctor
  F::Functor # on the schemas
  dom::D
  codom::C
  comma_cats::CC

  function SigmaMigration(F::Functor, dom::D, codom::C) where {D, C}
    cc = get_comma_cats(F)
    new{D, C, typeof(cc)}(F, dom, codom, cc)
  end
end

"""   Sigma(F::Functor)

Given a functor ``F: \\mathcal{C} \\to \\mathcal{D}`` produces a `MigrationFunctor`
which maps a ``\\mathcal{C}``-set ``X`` to the ``\\mathcal{D}``-set ``\\Sigma_F(X)``.
``\\Sigma_F`` is left-adjoint to ``\\Delta_F``.

For ``d \\in \\mathsf{ob}\\mathcal{D}``,
``\\Sigma_F(X)(d) := \\mathsf{colim}_{F \\downarrow d} X \\circ \\pi`` where
``\\pi: F\\downarrow d \\to \\mathcal{C}`` is the projection.

See (Spivak, 2014, *Category Theory for the Sciences*) for details.
"""
Sigma(F::Functor, dom, codom) = SigmaMigration(F, dom, codom)

function (ΣF::SigmaMigration)(Y::ACSet, X::ACSet)
  comma_cats = ΣF.comma_cats
  diagramD = FreeDiagram(codom(ΣF.F))

  # define Y on objects by taking colimits
  colimX = map(parts(diagramD, :V)) do i
    F∇d = ob(comma_cats, i)
    Xobs = map(ob(F∇d)) do (c,_)
      FinSet{Int, Int}(nparts(X, nameof(c)))
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
      universal(colimX[src(diagramD, g)],
        Multicospan(legs(colimX[tgt(diagramD, g)])[hom(comma_cats, g)[:V].func])
      ).func
    )
  end
  return Y
end


"""   inv(D::AbstractDict)

Given a dictionary `D` returns a function that maps a proposed value
`y` to the array of all keys with value `y`.
"""
inv(D::AbstractDict) = y -> [k for (k,v) in D if v == y]


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
function get_comma_cats(F::Functor)
  diagramD = FreeDiagram(codom(F))
  FObInv = inv(Ob(F)); FHomInv = inv(Hom(F))
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
###############################################################
"""Get the Schema from an ACSet
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


# Chase Algorithm
#################

add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

"""Create a ACSet instance modeling a C-Rel from an instance of an ACSet"""
function crel(x::StructACSet{S}) where {S}
  name = Symbol("Rel_$(typeof(x).name.name)")
  os, hs, _, _, src, tgt = S.parameters
  pres = Presentation(FreeSchema)
  nv = length(os)
  alledge = Symbol[]
  xobs = [Ob(FreeSchema, sym) for sym in vcat(os...,hs...)]
  for x in xobs
    add_generator!(pres, x)
  end
  for (i,h) in enumerate(hs)
    s, t = add_srctgt(h)
    add_generator!(pres, Hom(s, xobs[nv+i], xobs[src[h]]))
    add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt[h]]))
    append!(alledge, [s,t])
  end
  expr = struct_acset(name, StructACSet, pres, index=alledge)
  eval(expr)
  rel = eval(name)
  J = Base.invokelatest(rel)

  # initialize the C-Rel with x which satisfies the laws
  for o in ob(S)
    add_parts!(J, o, nparts(x, o))
  end
  src, tgt = dom(S), codom(S)
  for (i, d) in enumerate(hom(S))
    hs, ht = add_srctgt(d)
    add_parts!(J, d, nparts(x, src[i]))
    set_subpart!(J, hs, parts(x, src[i]))
    set_subpart!(J, ht, x[d])
  end
  return J
end

"""Convert a C-Rel back to a C-Set, fail if relations are not functional"""
function uncrel(J::StructACSet, I::StructACSet{S}) where {S}
  res = typeof(I)()
  for o in ob(S)
    add_parts!(res, o, nparts(J, o))
  end
  for m in hom(S)
    msrc, mtgt = add_srctgt(m)
    md, mcd = zip(sort(collect(zip(J[msrc], J[mtgt])))...)
    collect(md) == collect(1:length(md)) || error("nonfunctional $J")
    set_subpart!(res, m, mcd)
  end
  return res
end

"""Evaluate a possibly composite composition on a subset of the domain"""
function eval_path(pth, J::StructACSet, xs::Set{Int})::Set{Int}
  pthkind = typeof(pth).parameters[1]  # Warning: uses implementation details
  if pthkind == :id
    return xs
  elseif pthkind == :generator
    args = [pth]
  elseif pthkind == :compose
    args = pth.args
  else
    error(pthkind)
  end
  # Iteratively update X to Y by searching through all (x,y) in R ⊆ X×Y
  for m in map(Symbol, args)
    msrc, mtgt = add_srctgt(m)
    if isempty(xs)
      return xs
    else
      newxs = Set{Int}()
      for (jx, jy) in zip(J[msrc], J[mtgt])
        if jx ∈ xs
          push!(newxs, jy)
        end
      end
      xs = newxs
    end
  end
  return xs
end

"""
Chase algorithm as described by Spivak and Wisnesky in "Fast Left-Kan Extensions
Using The Chase"

Todo: handle attributes
"""
function chase(F::Functor, I::StructACSet{IS}, codomI::StructACSet{S};
               n::Int=8, verbose::Bool=false)::StructACSet{S} where {IS, S}
  J = crel(codomI) # pre-model data structure, initialized with codomI
  η = Dict() # mapping into J from I

  # Further initialize J using the domain instance, I
  for c in generators(dom(F), :Ob)
    η[c] = add_parts!(J, Symbol(Ob(F)[c]), nparts(I, Symbol(c)))
  end
  changed = false # iterate until no change or n is reached
  for counter in 1:n
    if verbose
      println("----- ITERATION $counter ------")
    end

    # Initialize equivalence relations for each component
    eqclasses = Dict([o=>IntDisjointSets(nparts(J, o)) for o in ob(S)])
    changed = false

    # Action α: add new elements when a function is dangling
    fresh = Dict{Symbol, Set{Int}}([o=>Set{Int}() for o in ob(S)])
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      xs = setdiff(parts(J, ddom), J[dsrc] ∪ fresh[ddom])
      for x in xs  # no y such that (x,y) ∈ J(d) and no fresh x
        gx = add_part!(J, dcodom) # add a fresh symbol
        if verbose
          println("α: $d($ddom#$x) ADDED $dcodom $gx")
        end
        add_part!(J, d; Dict([dsrc=>x, dtgt=>gx])...)
        gx_ = push!(eqclasses[dcodom])
        push!(fresh[dcodom], gx)
        gx == gx_ || error("Unexpected mismatch: $eqclasses \n$J")
        changed = true
      end
    end

    # Action βd: add all coincidences induced by D (i.e. fire EGDs)
    for (p, q) in equations(codom(F))
      for x in parts(J, Symbol(dom(p)))
        for px in eval_path(p, J, Set([x]))
          for qx in eval_path(q, J, Set([x]))
            union!(eqclasses[Symbol(codom(p))], px, qx)
            if verbose && px != qx
              println("βF: $p=$q MERGED $(codom(p)) $px = $qx")
            end
            changed |= px != qx # flip iff changed = ⊥ AND px != qx
          end
        end
      end
    end

    # Action βF: add all coincidences induced by F. Naturality square constraint
    for mg in generators(dom(F), :Hom)
      m, Fm, Fmcodom = map(Symbol, [mg, Hom(F)[mg], Ob(F)[codom(mg)]])
      is_id = typeof(Hom(F)[mg]).parameters[1] == :id
      for (x, mx) in enumerate(I[m])
        mα = η[codom(mg)][mx]
        Fms, Fmt = add_srctgt(Fm)
        αx = η[dom(mg)][x]
        αm = is_id ? αx : J[Fmt][incident(J, αx, Fms)[1]]
        union!(eqclasses[Fmcodom], mα, αm)
        if verbose && mα != αm
          println("βF: $mg ($(dom(mg))#$x) MERGED $Fmcodom $mα = $αm")
        end
        changed |= mα != αm # flip iff changed = ⊥ AND mα != αm
      end
    end

    # Action δ: add all coincidences induced by functionality
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      for x in parts(J, ddom)
        eq_ys = collect(Set(J[dtgt][incident(J, x, dsrc)]))
        for (y1, y2) in zip(eq_ys, eq_ys[2:end])
          union!(eqclasses[dcodom], y1, y2)
          if verbose
            println("δ: $d($ddom#$x) MERGED $dcodom $y1 = $y2")
          end
          changed = true
        end
      end
    end

    # Action γ: merge coincidentally equal elements
    μ = Dict{Symbol, Vector{Pair{Int,Int}}}([o=>Pair{Int,Int}[] for o in ob(S)])
    delob = Dict{Symbol, Vector{Int}}([o=>Int[] for o in ob(S)])
    for (o, eq) in pairs(eqclasses)
      eqsets = Dict{Int,Set{Int}}()
      # Recover the equivalence classes from the union-find structure
      for x in parts(J, o)
        eqrep = find_root(eq, x)
        if haskey(eqsets, eqrep)
          push!(eqsets[eqrep], x)
        else
          eqsets[eqrep] = Set([x])
        end
      end
      if verbose
        println("eqset $o $(values(eqsets))")
      end
      # Minimum element is the representative
      for vs in values(eqsets)
        m = minimum(vs)
        delete!(vs, m)
        append!(μ[o], [v=>m for v in vs])
        append!(delob[o], collect(vs))
      end
    end
    # Replace all instances of a class with its representative in J and η
    for (d, ddom, dcodom) in zip(hom(S), dom(S), codom(S))
      dsrc, dtgt = add_srctgt(d)
      isempty(μ[ddom]) || set_subpart!(J, dsrc, replace(J[dsrc], μ[ddom]...))
      isempty(μ[dcodom]) || set_subpart!(J, dtgt, replace(J[dtgt], μ[dcodom]...))
      # remove redundant duplicate relation rows
      seen = Set()
      for (i, st) in enumerate(zip(J[dsrc], J[dtgt]))
        if st ∈ seen
          rem_part!(J, d, i)
        else
          push!(seen, st)
        end
      end
    end
    for (Iob, mapping) in collect(η)
      reps = μ[Symbol(Ob(F)[Iob])]
      if !isempty(reps)
        η[Iob] = replace(mapping, reps...)
      end
    end
    for (o, vs) in collect(delob)
      isempty(vs) || rem_parts!(J, o, sort(vs))
    end
    if !changed
      break # termination condition
    end
  end

  if changed
    error("Chase did not terminate with $n steps: $J")
  else
    return uncrel(J, codomI)
  end
end


end #module

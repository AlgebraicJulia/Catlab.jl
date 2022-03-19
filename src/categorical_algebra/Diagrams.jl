""" Diagrams in a category and their morphisms.
"""
module Diagrams
export Diagram, DiagramHom, id, op, co, shape, diagram, shape_map, diagram_map

using AutoHashEquals

using ...GAT
import ...Theories: dom, codom, id, compose, ⋅, ∘, munit, oplus, otimes
using ...Theories: Category, composeH
import ..Categories: ob_map, hom_map
using ..FinCats, ..FreeDiagrams
using ..FinCats: mapvals
import ..FinCats: force, collect_ob, collect_hom
import ..Limits: limit, colimit, universal, equalizer, product, Limit, Colimit,
                 incl, proj, pullback, coproduct, coequalizer, copair, pushout,
                 AbstractLimit, Product, Coproduct, AbstractColimit

# TODO: Implement these functions more generally, and move elsewhere.

""" Opposite of a category or, more generally, 1-cell dual of a 2-category.
"""
function op end

""" 2-cell dual of a 2-category.
"""
function co end

# Data types
############

""" Diagram in a category.

Recall that a *diagram* in a category ``C`` is a functor ``D: J → C``, where for
us the *shape category* ``J`` is finitely presented. Although such a diagram is
captured perfectly well by a `FinDomFunctor`, there are several different
notions of morphism between diagrams. This simple wrapper type exists to
distinguish them. See [`DiagramHom`](@ref) for more about the morphisms.
"""
struct Diagram{T,C<:Cat,D<:Functor{<:FinCat,C}}
  diagram::D
end
Diagram{T}(F::D) where {T,C<:Cat,D<:Functor{<:FinCat,C}} = Diagram{T,C,D}(F)

Diagram{T}(d::Diagram) where T = Diagram{T}(d.diagram)
Diagram(args...) = Diagram{id}(args...)

""" Functor underlying a diagram object.
"""
diagram(d::Diagram) = d.diagram

""" The *shape* or *indexing category* of a diagram.

This is the domain of the underlying functor.
"""
shape(d::Diagram) = dom(diagram(d))

Base.hash(d::Diagram{T}, h::UInt) where {T} = hash(T, hash(diagram(d), h))

Base.:(==)(d1::Diagram{T}, d2::Diagram{S}) where {T,S} =
  T == S && diagram(d1) == diagram(d2)

ob_map(d::Diagram, x) = ob_map(diagram(d), x)
hom_map(d::Diagram, f) = hom_map(diagram(d), f)

force(d::Diagram{T}) where T = Diagram{T}(force(diagram(d)))

function Base.show(io::IO, d::Diagram{T}) where T
  print(io, "Diagram{$T}(")
  show(io, diagram(d))
  print(io, ")")
end

""" Morphism of diagrams in a category.

In fact, this type encompasses several different kinds of morphisms from a
diagram ``D: J → C`` to another diagram ``D′: J′ → C``:

1. `DiagramHom{id}`: a functor ``F: J → J′`` together with a natural
   transformation ``ϕ: D ⇒ F⋅D′``
2. `DiagramHom{op}`: a functor ``F: J′ → J`` together with a natural
   transformation ``ϕ: F⋅D ⇒ D′``
3. `DiagramHom{co}`: a functor ``F: J → J′`` together with a natural
   transformation ``ϕ: F⋅D′ ⇒ D``.

Note that `Diagram{op}` is *not* the opposite category of `Diagram{id}`, but
`Diagram{op}` and `Diagram{co}` are opposites of each other. Explicit support is
included for both because they are useful for different purposes: morphisms of
type `DiagramHom{op}` induce morphisms between the limits of the diagrams,
whereas morphisms of type `DiagramHom{co}` generalize morphisms of polynomial
functors.
"""
struct DiagramHom{T,C<:Cat,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C}}
  shape_map::F
  diagram_map::Φ
  precomposed_diagram::D
end
DiagramHom{T}(shape_map::F, diagram_map::Φ, precomposed_diagram::D) where
    {T,C,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C}} =
  DiagramHom{T,C,F,Φ,D}(shape_map, diagram_map, precomposed_diagram)

DiagramHom{T}(f::DiagramHom) where T =
  DiagramHom{T}(f.shape_map, f.diagram_map, f.precomposed_diagram)
DiagramHom(args...) = DiagramHom{id}(args...)

DiagramHom{T}(ob_maps, hom_map, D::Diagram{T}, D′::Diagram{T}) where T =
  DiagramHom{T}(ob_maps, hom_map, diagram(D), diagram(D′))
DiagramHom{T}(ob_maps, D::Union{Diagram{T},FinDomFunctor},
              D′::Union{Diagram{T},FinDomFunctor}) where T =
  DiagramHom{T}(ob_maps, nothing, D, D′)

function DiagramHom{id}(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor)
  f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′))
  DiagramHom{id}(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′)
end
function DiagramHom{op}(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor)
  f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D′), dom(D))
  DiagramHom{op}(f, mapvals(x -> cell2(D,x), ob_maps), D, D′)
end
function DiagramHom{co}(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor)
  f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′))
  DiagramHom{co}(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′)
end

function DiagramHom{id}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor)
  ϕ = FinTransformation(components, D, f⋅D′)
  DiagramHom{id}(f, ϕ, D′)
end
function DiagramHom{op}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor)
  ϕ = FinTransformation(components, f⋅D, D′)
  DiagramHom{op}(f, ϕ, D)
end
function DiagramHom{co}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor)
  ϕ = FinTransformation(components, f⋅D′, D)
  DiagramHom{co}(f, ϕ, D′)
end

cell1(pair::Union{Pair,Tuple{Any,Any}}) = first(pair)
cell1(x) = x
cell2(D::FinDomFunctor, pair::Union{Pair,Tuple{Any,Any}}) = last(pair)
cell2(D::FinDomFunctor, x) = id(codom(D), ob_map(D, x))

shape_map(f::DiagramHom) = f.shape_map
diagram_map(f::DiagramHom) = f.diagram_map

Base.hash(f::DiagramHom{T}, h::UInt) where {T} = hash(T, hash(f.shape_map,
  hash(f.diagram_map, hash(f.precomposed_diagram, h))))

Base.:(==)(f::DiagramHom{T}, g::DiagramHom{S}) where {T,S} =
  T == S && shape_map(f) == shape_map(g) && diagram_map(f) == diagram_map(g) &&
  f.precomposed_diagram == g.precomposed_diagram

ob_map(f::DiagramHom, x) = (ob_map(f.shape_map, x), component(f.diagram_map, x))
hom_map(f::DiagramHom, g) = hom_map(f.shape_map, g)

collect_ob(f::DiagramHom) =
  collect(zip(collect_ob(f.shape_map), components(f.diagram_map)))
collect_hom(f::DiagramHom) = collect_hom(f.shape_map)

function Base.show(io::IO, f::DiagramHom{T}) where T
  J = dom(shape_map(f))
  print(io, "DiagramHom{$T}([")
  join(io, mapvals(x -> ob_map(f,x), ob_generators(J), iter=true), ", ")
  print(io, "], [")
  join(io, mapvals(g -> hom_map(f,g), hom_generators(J), iter=true), ", ")
  print(io, "], ")
  show(IOContext(io, :compact=>true, :hide_domains=>true), diagram(dom(f)))
  print(io, ", ")
  show(IOContext(io, :compact=>true, :hide_domains=>true), diagram(codom(f)))
  print(io, ")")
end

# Categories of diagrams
########################

dom_diagram(f::DiagramHom{id}) = dom(diagram_map(f))
dom_diagram(f::DiagramHom{op}) = f.precomposed_diagram
dom_diagram(f::DiagramHom{co}) = codom(diagram_map(f))
codom_diagram(f::DiagramHom{id}) = f.precomposed_diagram
codom_diagram(f::DiagramHom{op}) = codom(diagram_map(f))
codom_diagram(f::DiagramHom{co}) = f.precomposed_diagram

dom(f::DiagramHom{T}) where T = Diagram{T}(dom_diagram(f))
codom(f::DiagramHom{T}) where T = Diagram{T}(codom_diagram(f))

function id(d::Diagram{T}) where T
  F = diagram(d)
  DiagramHom{T}(id(dom(F)), id(F), F)
end

function compose(f::DiagramHom{id}, g::DiagramHom{id})
  DiagramHom{id}(
    shape_map(f) ⋅ shape_map(g),
    diagram_map(f) ⋅ (shape_map(f) * diagram_map(g)),
    codom_diagram(g))
end
function compose(f::DiagramHom{op}, g::DiagramHom{op})
  DiagramHom{op}(
    shape_map(g) ⋅ shape_map(f),
    (shape_map(g) * diagram_map(f)) ⋅ diagram_map(g),
    dom_diagram(f))
end
function compose(f::DiagramHom{co}, g::DiagramHom{co})
  DiagramHom{co}(
    shape_map(f) ⋅ shape_map(g),
    (shape_map(f) * diagram_map(g)) ⋅ diagram_map(f),
    codom_diagram(g))
end

# TODO: The diagrams in a category naturally form a 2-category, but for now we
# just implement the category struture.

@instance Category{Diagram,DiagramHom} begin
  @import dom, codom, compose, id
end

op(d::Diagram{op}) = Diagram{co}(d)
op(d::Diagram{co}) = Diagram{op}(d)
op(f::DiagramHom{op}) = DiagramHom{co}(f)
op(f::DiagramHom{co}) = DiagramHom{op}(f)

# Any functor ``F: C → D`` induces a functor ``Diag(F): Diag(C) → Diag(D)`` by
# post-composition and post-whiskering.

function compose(d::Diagram{T}, F::Functor; kw...) where T
  Diagram{T}(compose(diagram(d), F; kw...))
end
function compose(f::DiagramHom{T}, F::Functor; kw...) where T
  DiagramHom{T}(shape_map(f), composeH(diagram_map(f), F; kw...),
                compose(f.precomposed_diagram, F; kw...))
end

# Limits and colimits
#####################

# In a cocomplete category `C`, colimits define a functor `Diag{id,C} → C`.
# Dually, in a complete category `C`, limits define functor `Diag{op,C} → C`.

limit(d::Diagram{op}; alg=nothing) = limit(diagram(d), alg)
colimit(d::Diagram{id}; alg=nothing) = colimit(diagram(d), alg)


function universal(f::DiagramHom{op}, dom_lim, codom_lim)
  J′ = shape(codom(f))
  cone = Multispan(apex(dom_lim), map(ob_generators(J′)) do j′
    j, g = ob_map(f, j′)
    πⱼ = legs(dom_lim)[j]
    compose(πⱼ, g)
  end)
  universal(codom_lim, cone)
end

function universal(f::DiagramHom{id}, dom_colim, codom_colim)
  J = shape(dom(f))
  cocone = Multicospan(apex(codom_colim), map(ob_generators(J)) do j
    j′, g = ob_map(f, j)
    ιⱼ′ = legs(codom_colim)[j′]
    compose(g, ιⱼ′)
  end)
  universal(dom_colim, cocone)
end

# Monads of diagrams
####################

# TODO: Define monad multiplications that go along with the units.

function munit(::Type{Diagram{T}}, C::Cat, x; shape=nothing) where T
  if isnothing(shape)
    shape = FinCat(1)
  else
    @assert is_discrete(shape) && length(ob_generators(shape)) == 1
  end
  Diagram{T}(FinDomFunctor([x], shape, C))
end

function munit(::Type{DiagramHom{T}}, C::Cat, f;
               dom_shape=nothing, codom_shape=nothing) where T
  f = hom(C, f)
  d = munit(Diagram{T}, C, dom(C, f), shape=dom_shape)
  d′= munit(Diagram{T}, C, codom(C, f), shape=codom_shape)
  j = only(ob_generators(shape(d′)))
  DiagramHom{T}([Pair(j, f)], d, d′)
end


# (co)Limits in Category of Diagrams
####################################

"""
Product of diagrams in the same category. (coproduct for :op morphisms)
"""
function diagram_hom_product(Xs::AbstractVector{<: Diagram{T}}; kw...) where T

  # Collect / validate type information about the input
  cod = codom(diagram(first(Xs))) # the category the diagrams are in
  is_id = T == id
  is_id || T == op || error("Diagrams of type $T not supported")
  # Equality of typecat too strict, but in theory this should be checked
  # cods = Set([codom(diagram(x)) for x in Xs])
  # length(cods) == 1 || error("Can't take product of diagrams in different cats")

  # Collect data about the product of the shape categories
  P = product([dom(diagram(x)) for x in Xs])
  obs, homs = map([ob_map=>ob_generators, hom_map=>hom_generators]) do (F, gen)
   [tuple([F(l, g) for l in legs(P)]...) for g in gen(apex(P))]
  end;

  # Take (co)products of objects in the underlying category
  omap, nat, base_prod = Dict(), Dict(), Dict()
  for os in obs
    lim = is_id ? product : coproduct
    base_prod[os] = p = lim([ob_map(diagram(X), o) for (o, X) in (zip(os, Xs))])
    s = Symbol(os)
    omap[s] = apex(p)
    nat[s] = legs(p)
  end

  hmap = Dict(map(homs) do hs
    maps = [hom_map(diagram(X), o) for (o, X) in (zip(hs, Xs))]
    Symbol(hs) => (is_id ? otimes : oplus)(maps)
  end)

  # Assemble product diagram
  apx = Diagram{T}(FinDomFunctor(omap, hmap, apex(P), cod))
  ls = map(enumerate(zip(legs(P), Xs))) do (i, (l, X))
    η = Dict([k=>v[i] for (k,v) in nat])
    src, tgt = is_id ? (apx, X) : (X, apx)
    DiagramHom{T}(l, η, src, tgt)
  end;
  return P, base_prod, Vector{DiagramHom{T}}(ls)
end

"""
Computes the equalizer (for id morphisms) / coequalizer (for op morphisms)
"""
function diagram_hom_equalizer(fs::AbstractVector{<: DiagramHom{T}}) where T
  # Collect / validate type information about the input
  X, Y = diagram.(only.(Set.([dom.(fs), codom.(fs)])));
  is_id = T == id
  is_id || T == op || error("diagram hom of type $T not supported")
  eq, eq_incl = is_id ? (equalizer, incl) : (coequalizer, proj)
  cod = codom(diagram(dom(first(fs))))
  # Equality of typecat too strict, but in theory this should be checked
  # cods = Set([codom(diagram(x)) for x in Xs])
  # cod = only(Set(vcat([codom.(diagram.([dom(x),codom(x)])) for x in fs]...)))

  # Shape level equalizer
  shape_eq = equalizer(shape_map.(fs))
  Eshape = apex(shape_eq)

  # Underlying (co)equalizer on natural transformations
  eqs = Dict(map(ob_generators(Eshape)) do o
    o=>eq([diagram_map(f)[o] for f in fs])
  end)
  η = Dict([o=>eq_incl(e) for (o,e) in collect(eqs)])

  om_ = Dict([o=>apex(e) for (o,e) in collect(eqs)])
  hm_ = Dict(map(hom_generators(Eshape)) do h
    h => compose(η[dom(h)], hom_map(is_id ? X : Y, h))
  end)

  # Assemble diagram morphism
  E = Diagram{T}(FinDomFunctor(om_,hm_,Eshape, cod))
  src, tgt = is_id ? (diagram(E), X) : (Y, diagram(E))
  l = DiagramHom{T}(incl(shape_eq), η, src, tgt)
  return shape_eq, eqs, l
end


"""
Coproduct of diagrams in the same category. (product for op morphisms)
"""
function diagram_hom_coproduct(Xs::AbstractVector{<: Diagram{T}}; kw...) where {T}
  # Collect / validate type information about the input
  is_id = T == id
  is_id || T == op || error("Diagrams of type $T not supported")
  cod = codom(diagram(first(Xs))) # the category the diagrams are in
  # Equality of typecat too strict, but in theory this should be checked
  # cod = only(Set([codom(diagram(x)) for x in Xs]))

  # Shape level coproduct
  hcprod = coproduct(FinCatPresentation[dom(diagram(x)) for x in Xs])

  # Inclusion of data in underlying category
  obs, homs = Dict(), Dict()
  for (l, X) in zip(legs(hcprod), Xs)
    for (k,v) in diagram(X).ob_map
      obs[ob_map(l, k)] = v
    end
    for (k,v) in diagram(X).hom_map
      homs[hom_map(l, k)] = v
    end
  end

  # Assemble diagram morphism
  apx = Diagram{T}(FinDomFunctor(obs,homs, apex(hcprod), cod))
  ls = map(zip(legs(hcprod), Xs)) do (l, X)
    eta = Dict(k => id(v) for (k, v) in diagram(X).ob_map)
    src, tgt = diagram.(is_id ? [X, apx] : [apx, X])
    DiagramHom{T}(l, eta, src, tgt)
  end;
  return hcprod, Dict(), ls
end
# const Product{Ob} = AbstractLimit{Ob,<:DiscreteDiagram}

@auto_hash_equals struct DiagLimit{
  Ob,Diagram,LimType<:Union{Limit,Colimit},Cone<:Multispan{Ob}
    } <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  shapelim::LimType
  baselim::Dict
  cone::Cone
end


@auto_hash_equals struct DiagColimit{
  Ob,Diagram,LimType<:Union{Limit,Colimit},Cocone<:Multicospan{Ob}
    } <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  shapelim::LimType
  baselim::Dict
  cocone::Cocone
end

product(Xs::AbstractVector{<: Diagram{id}}; kw...) =
  let r = diagram_hom_product(Xs)
  DiagLimit(DiscreteDiagram(Xs), r[1], r[2], Multispan(r[3])) end

coproduct(Xs::AbstractVector{<: Diagram{id}}; kw...) =
  let (sl, dl, csp) = diagram_hom_coproduct(Xs)
  DiagColimit(DiscreteDiagram(Xs), sl, dl, Multicospan(csp)) end

product(Xs::AbstractVector{<: Diagram{op}}; kw...) =
  let r = diagram_hom_coproduct(Xs)
  DiagLimit(DiscreteDiagram(Xs), r[1], r[2], Multispan(r[3])) end

coproduct(Xs::AbstractVector{<: Diagram{op}}; kw...) =
  let r = diagram_hom_product(Xs)
  DiagColimit(DiscreteDiagram(Xs), r[1], r[2], Multicospan(r[3])) end

equalizer(fs::AbstractVector{<: DiagramHom{id}}) =
  let r = diagram_hom_equalizer(fs)
  DiagLimit(ParallelMorphisms(fs), r[1], r[2], Multispan([r[3]])) end

coequalizer(fs::AbstractVector{<: DiagramHom{op}}) =
  let r = diagram_hom_equalizer(fs)
  DiagColimit(ParallelMorphisms(fs), r[1], r[2], Multicospan([r[3]])) end

function pullback(fs::Multicospan{<:Diagram{T}, <: DiagramHom{T}}) where {T}
  p = product(Diagram{T}[dom(f) for f in fs])
  equalizer(DiagramHom{T}[compose(l, f) for (l,f) in zip(legs(p), fs)])
end

function pushout(fs::Multispan{<:Diagram{T}, <: DiagramHom{T}}) where {T}
  cp = coproduct(Diagram{T}[codom(f) for f in fs])
  coequalizer(DiagramHom{op}[compose(f,l) for (l,f) in zip(legs(cp), fs)])
end

function universal(p::DiagLimit{<:Diagram{id},<:DiscreteDiagram}, sp::Multispan)
  a_p, a_sp = apex.([p, sp])
  s_map = universal(p.shapelim, Multispan(shape_map.(legs(sp))))
  d_map = Dict(map(ob_generators(dom(diagram(a_sp)))) do o
    d_tgts = [diagram_map(l)[o] for l in sp]
    tgts = tuple([ob_map(shape_map(l),o) for l in sp]...)
    o => universal(p.baselim[tgts], Multispan(d_tgts))
  end)
  DiagramHom{id}(s_map, d_map, a_sp, a_p)
end


function universal(p::DiagLimit{<:Diagram{op},<:DiscreteDiagram}, sp::Multispan)
  a_p, a_sp = apex.([p, sp])
  s_map = universal(p.shapelim, Multicospan(shape_map.(legs(sp))))
  d_map = Dict()
  for (spl, pl) in zip(legs(sp),legs(p))
    for (k,v) in components(diagram_map(spl))
      d_map[ob_map(shape_map(pl),k)] = v
    end
  end
  DiagramHom{op}(s_map, d_map, a_sp, a_p)
end

function universal(cp::DiagColimit{<:Diagram{id},<:DiscreteDiagram}, csp::Multicospan)
  a_cp, a_csp = apex.([cp, csp])
  s_map = universal(cp.shapelim, Multicospan(shape_map.(legs(csp))))
  d_map = Dict()
  for (cspl, cpl) in zip(legs(csp),legs(cp))
    for o in ob_generators(dom(diagram(dom(cpl))))
      d_map[Symbol(ob_map(shape_map(cpl), o))] = diagram_map(cspl)[o]
    end
  end
  DiagramHom{id}(s_map, d_map, a_cp, a_csp)
end

function universal(p::DiagColimit{<:Diagram{op},<:DiscreteDiagram}, sp::Multicospan)
  a_p, a_sp = apex.([p, sp])
  s_map = universal(p.shapelim, Multispan(shape_map.(legs(sp))))
  d_map = Dict(map(ob_generators(dom(diagram(a_sp)))) do o
    d_tgts = [diagram_map(l)[o] for l in sp]
    tgts = tuple([ob_map(shape_map(l),o) for l in sp]...)
    o => universal(p.baselim[tgts], Multicospan(d_tgts))
  end)
  DiagramHom{op}(s_map, d_map, a_p, a_sp)
end


function factorize(eq::DiagLimit{<:Diagram{T},<:ParallelPair}, f::DiagramHom{T}) where T
  a_eq = apex(eq)
  s_map = factorize(eq.shapelim, shape_map(f))
  d_map = nothing # todo
  DiagramHom{id}(s_map, d_map, dom(f), codom(a_eq))
end

end # module
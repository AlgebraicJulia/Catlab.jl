""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
pairs of objects, discrete diagrams, parallel pairs, composable pairs, and spans
and cospans. Limits and colimits are most commonly taken over free diagrams.
"""
module FreeDiagrams
export FixedShapeFreeDiagram, FreeDiagram, SchFreeDiagram,
  BipartiteFreeDiagram, SchBipartiteFreeDiagram,
  DiscreteDiagram, EmptyDiagram, SingletonDiagram, ObjectPair,
  Span, Cospan, Multispan, Multicospan, SMultispan, SMulticospan,
  ParallelPair, ParallelMorphisms, ComposablePair, ComposableMorphisms,
  diagram_type, cone_objects, cocone_objects, cocone_indices,
  ob, hom, dom, codom, apex, legs, feet, left, right, bundle_legs,
  nv, ne, src, tgt, vertices, edges, has_vertex, has_edge,
  add_vertex!, add_vertices!, add_edge!, add_edges!,
  ob₁, ob₂, nv₁, nv₂, vertices₁, vertices₂,
  add_vertex₁!, add_vertex₂!, add_vertices₁!, add_vertices₂!

using StructEquality
using StaticArrays: StaticVector, SVector

using ACSets
using ...Present, ...Theories, ...Graphs, ..FinCats
import ...Theories: ob, hom, dom, codom
import ..FinCats: FreeCatGraph, FinDomFunctor, collect_ob, collect_hom

# Diagram interface
###################

""" Given a diagram in a category ``C``, return Julia type of objects and
morphisms in ``C`` as a tuple type of form ``Tuple{Ob,Hom}``.
"""
function diagram_type end

""" Objects in diagram that will have explicit legs in limit cone.

In category theory, it is common practice to elide legs of limit cones that can
be computed from other legs, especially for diagrams of certain fixed shapes.
For example, when it taking a pullback (the limit of a cospan), the limit object
is often treated as having two projections, rather than three. This function
encodes such conventions by listing the objects in the diagram that will have
corresponding legs in the limit object created by Catlab.

See also: [`cocone_objects`](@ref).
"""
cone_objects(diagram) = ob(diagram)

""" Objects in diagram that will have explicit legs in colimit cocone.

See also: [`cone_objects`](@ref).
"""
cocone_objects(diagram) = ob(diagram)

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedShapeFreeDiagram{Ob,Hom} end

diagram_type(::FixedShapeFreeDiagram{Ob,Hom}) where {Ob,Hom} = Tuple{Ob,Hom}

# Discrete diagrams
#------------------

""" Discrete diagram: a diagram with no non-identity morphisms.
"""
@struct_hash_equal struct DiscreteDiagram{Ob,Hom,Obs<:AbstractVector{Ob}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  objects::Obs
end

DiscreteDiagram(objects::Obs, Hom::Type=Any) where {Ob,Obs<:AbstractVector{Ob}} =
  DiscreteDiagram{Ob,Hom,Obs}(objects)

const EmptyDiagram{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{0,Ob}}
const SingletonDiagram{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{1,Ob}}
const ObjectPair{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{2,Ob}}

EmptyDiagram{Ob}(Hom::Type=Any) where Ob = DiscreteDiagram(SVector{0,Ob}(), Hom)
SingletonDiagram(ob, Hom::Type=Any) = DiscreteDiagram(SVector(ob), Hom)
ObjectPair(first, second, Hom::Type=Any) =
  DiscreteDiagram(SVector(first, second), Hom)

ob(d::DiscreteDiagram) = d.objects

Base.iterate(d::DiscreteDiagram, args...) = iterate(d.objects, args...)
Base.eltype(d::DiscreteDiagram) = eltype(d.objects)
Base.length(d::DiscreteDiagram) = length(d.objects)
Base.getindex(d::DiscreteDiagram, i) = d.objects[i]
Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)
Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

# Spans and cospans
#------------------

""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@struct_hash_equal struct Multispan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  apex::Ob
  legs::Legs
end

function Multispan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(dom.(legs)) || error("Legs $legs do not have common domain")
  Multispan(dom(first(legs)), legs)
end

const SMultispan{N,Ob,Hom} = Multispan{Ob,Hom,<:StaticVector{N,Hom}}

SMultispan{N}(apex, legs::Vararg{Any,N}) where N =
  Multispan(apex, SVector{N}(legs...))
SMultispan{0}(apex) = Multispan(apex, SVector{0,typeof(id(apex))}())
SMultispan{N}(legs::Vararg{Any,N}) where N = Multispan(SVector{N}(legs...))

""" Span of morphims in a category.

A common special case of [`Multispan`](@ref). See also [`Cospan`](@ref).
"""
const Span{Ob,Hom} = SMultispan{2,Ob,Hom}

""" Apex of multispan or multicospan.

The apex of a multi(co)span is the object that is the (co)domain of all the
[`legs`](@ref).
"""
apex(span::Multispan) = span.apex

""" Legs of multispan or multicospan.

The legs are the morphisms comprising the multi(co)span.
"""
legs(span::Multispan) = span.legs

""" Feet of multispan or multicospan.

The feet of a multispan are the codomains of the [`legs`](@ref).
"""
feet(span::Multispan) = map(codom, span.legs)

""" Left leg of span or cospan.
"""
left(span::Span) = span.legs[1]

""" Right leg of span or cospan.
"""
right(span::Span) = span.legs[2]

cocone_objects(span::Multispan) = feet(span)

Base.iterate(span::Multispan, args...) = iterate(span.legs, args...)
Base.eltype(span::Multispan) = eltype(span.legs)
Base.length(span::Multispan) = length(span.legs)

""" Multicospan of morphisms in a category.

A multicospan is like a [`Cospan`](@ref) except that it may have a number of
legs different than two. A limit of this shape is a pullback.
"""
@struct_hash_equal struct Multicospan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  apex::Ob
  legs::Legs
end

function Multicospan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(codom.(legs)) || error("Legs $legs do not have common codomain")
  Multicospan(codom(first(legs)), legs)
end

const SMulticospan{N,Ob,Hom} = Multicospan{Ob,Hom,<:StaticVector{N,Hom}}

SMulticospan{N}(apex, legs::Vararg{Any,N}) where N =
  Multicospan(apex, SVector{N}(legs...))
SMulticospan{0}(apex) = Multicospan(apex, SVector{0,typeof(id(apex))}())
SMulticospan{N}(legs::Vararg{Any,N}) where N = Multicospan(SVector{N}(legs...))

""" Cospan of morphisms in a category.

A common special case of [`Multicospan`](@ref). See also [`Span`](@ref).
"""
const Cospan{Ob,Hom} = SMulticospan{2,Ob,Hom}

apex(cospan::Multicospan) = cospan.apex
legs(cospan::Multicospan) = cospan.legs
feet(cospan::Multicospan) = map(dom, cospan.legs)
left(cospan::Cospan) = cospan.legs[1]
right(cospan::Cospan) = cospan.legs[2]

cone_objects(cospan::Multicospan) = feet(cospan)

Base.iterate(cospan::Multicospan, args...) = iterate(cospan.legs, args...)
Base.eltype(cospan::Multicospan) = eltype(cospan.legs)
Base.length(cospan::Multicospan) = length(cospan.legs)

""" Bundle together legs of a multi(co)span.

For example, calling `bundle_legs(span, SVector((1,2),(3,4)))` on a multispan
with four legs gives a span whose left leg bundles legs 1 and 2 and whose right
leg bundles legs 3 and 4. Note that in addition to bundling, this function can
also permute legs and discard them.

The bundling is performed using the universal property of (co)products, which
assumes that these (co)limits exist.
"""
bundle_legs(span::Multispan, indices) =
  Multispan(apex(span), map(i -> bundle_leg(span, i), indices))
bundle_legs(cospan::Multicospan, indices) =
  Multicospan(apex(cospan), map(i -> bundle_leg(cospan, i), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int) = legs(x)[i]
bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple) = bundle_leg(x, SVector(i))
bundle_leg(span::Multispan, i::AbstractVector{Int}) = pair(legs(span)[i])
bundle_leg(cospan::Multicospan, i::AbstractVector{Int}) = copair(legs(cospan)[i])

# Parallel morphisms
#-------------------

""" Parallel morphims in a category.

[Parallel morphisms](https://ncatlab.org/nlab/show/parallel+morphisms) are just
morphisms with the same domain and codomain. A (co)limit of this shape is a
(co)equalizer.

For the common special case of two morphisms, see [`ParallelPair`](@ref).
"""
@struct_hash_equal struct ParallelMorphisms{Dom,Codom,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Union{Dom,Codom},Hom}
  dom::Dom
  codom::Codom
  homs::Homs
end

function ParallelMorphisms(homs::AbstractVector)
  @assert !isempty(homs) && allequal(dom.(homs)) && allequal(codom.(homs))
  ParallelMorphisms(dom(first(homs)), codom(first(homs)), homs)
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Dom,Codom,Hom} =
  ParallelMorphisms{Dom,Codom,Hom,<:StaticVector{2,Hom}}

function ParallelPair(first, last)
  dom(first) == dom(last) ||
    error("Domains of parallel pair do not match: $first vs $last")
  codom(first) == codom(last) ||
    error("Codomains of parallel pair do not match: $first vs $last")
  ParallelMorphisms(dom(first), codom(first), SVector(first, last))
end

dom(para::ParallelMorphisms) = para.dom
codom(para::ParallelMorphisms) = para.codom
hom(para::ParallelMorphisms) = para.homs

cone_objects(para::ParallelMorphisms) = SVector(dom(para))
cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

Base.iterate(para::ParallelMorphisms, args...) = iterate(para.homs, args...)
Base.eltype(para::ParallelMorphisms) = eltype(para.homs)
Base.length(para::ParallelMorphisms) = length(para.homs)
Base.getindex(para::ParallelMorphisms, i) = para.homs[i]
Base.firstindex(para::ParallelMorphisms) = firstindex(para.homs)
Base.lastindex(para::ParallelMorphisms) = lastindex(para.homs)

allequal(xs::AbstractVector) = isempty(xs) || all(==(xs[1]), xs)

# Composable morphisms
#---------------------

""" Composable morphisms in a category.

Composable morphisms are a sequence of morphisms in a category that form a path
in the underlying graph of the category.

For the common special case of two morphisms, see [`ComposablePair`](@ref).
"""
@struct_hash_equal struct ComposableMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  homs::Homs
end

function ComposableMorphisms(homs::Homs) where {Hom, Homs<:AbstractVector{Hom}}
  doms, codoms = dom.(homs), codom.(homs)
  all(c == d for (c,d) in zip(codoms[1:end-1], doms[2:end])) ||
    error("Domain mismatch in composable sequence: $homs")
  ComposableMorphisms{Union{eltype(doms),eltype(codoms)},Hom,Homs}(homs)
end

""" Pair of composable morphisms in a category.

[Composable pairs](https://ncatlab.org/nlab/show/composable+pair) are a common
special case of [`ComposableMorphisms`](@ref).
"""
const ComposablePair{Ob,Hom} = ComposableMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

ComposablePair(first, last) = ComposableMorphisms(SVector(first, last))

dom(comp::ComposableMorphisms) = dom(first(comp))
codom(comp::ComposableMorphisms) = codom(last(comp))
hom(comp::ComposableMorphisms) = comp.homs

Base.iterate(comp::ComposableMorphisms, args...) = iterate(comp.homs, args...)
Base.eltype(comp::ComposableMorphisms) = eltype(comp.homs)
Base.length(comp::ComposableMorphisms) = length(comp.homs)
Base.getindex(comp::ComposableMorphisms, i) = comp.homs[i]
Base.firstindex(comp::ComposableMorphisms) = firstindex(comp.homs)
Base.lastindex(comp::ComposableMorphisms) = lastindex(comp.homs)

# Diagrams of flexible shape
############################

# Bipartite free diagrams
#------------------------

@abstract_acset_type _BipartiteFreeDiagram <: AbstractUndirectedBipartiteGraph

""" A free diagram with a bipartite structure.

Such diagrams include most of the fixed shapes, such as spans, cospans, and
parallel morphisms. They are also the generic shape of diagrams for limits and
colimits arising from undirected wiring diagrams. For limits, the boxes
correspond to vertices in ``V₁`` and the junctions to vertices in ``V₂``.
Colimits are dual.
"""
const BipartiteFreeDiagram{Ob,Hom,S} = _BipartiteFreeDiagram{S,Tuple{Ob,Hom}}

@present SchBipartiteFreeDiagram <: SchUndirectedBipartiteGraph begin
  Ob::AttrType
  Hom::AttrType
  ob₁::Attr(V₁, Ob)
  ob₂::Attr(V₂, Ob)
  hom::Attr(E, Hom)
end

""" The default concrete type for bipartite free diagrams.
"""
@acset_type BasicBipartiteFreeDiagram(SchBipartiteFreeDiagram,
  index=[:src, :tgt]) <: _BipartiteFreeDiagram

@present SchFreeDiagramAsBipartite <: SchBipartiteFreeDiagram begin
  V::Ob
  orig_vert₁::Hom(V₁, V)
  orig_vert₂::Hom(V₂, V)
end

""" A free diagram that has been converted to a bipartite free diagram.
"""
@acset_type FreeDiagramAsBipartite(SchFreeDiagramAsBipartite,
  index=[:src, :tgt], unique_index=[:orig_vert₁, :orig_vert₂]) <: _BipartiteFreeDiagram

ob₁(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₁)
ob₂(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₂)
hom(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :hom)

diagram_type(::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} = Tuple{Ob,Hom}
cone_objects(diagram::BipartiteFreeDiagram) = ob₁(diagram)
cocone_objects(diagram::BipartiteFreeDiagram) = ob₂(diagram)

BipartiteFreeDiagram{Ob,Hom}() where {Ob,Hom} =
  BasicBipartiteFreeDiagram{Ob,Hom}()

BipartiteFreeDiagram(obs₁::AbstractVector{Ob₁}, obs₂::AbstractVector{Ob₂},
                     homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob₁,Ob₂,Hom} =
  BipartiteFreeDiagram{Union{Ob₁,Ob₂},Hom}(obs₁, obs₂, homs)

function BipartiteFreeDiagram{Ob,Hom}(obs₁::AbstractVector, obs₂::AbstractVector,
                                      homs::AbstractVector) where {Ob,Hom}
  @assert all(obs₁[s] == dom(f) && obs₂[t] == codom(f) for (f,s,t) in homs)
  d = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(d, length(obs₁), ob₁=obs₁)
  add_vertices₂!(d, length(obs₂), ob₂=obs₂)
  add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

BipartiteFreeDiagram(d::FixedShapeFreeDiagram{Ob,Hom}; kw...) where {Ob,Hom} =
  BipartiteFreeDiagram{Ob,Hom}(d; kw...)

function BipartiteFreeDiagram{Ob,Hom}(discrete::DiscreteDiagram;
                                      colimit::Bool=false) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  if colimit
    add_vertices₂!(d, length(discrete), ob₂=collect(discrete))
  else
    add_vertices₁!(d, length(discrete), ob₁=collect(discrete))
  end
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(span::Multispan) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₁!(d, ob₁=apex(span))
  vs = add_vertices₂!(d, length(span), ob₂=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(cospan::Multicospan) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₂!(d, ob₂=apex(cospan))
  vs = add_vertices₁!(d, length(cospan), ob₁=feet(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(para::ParallelMorphisms) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₁ = add_vertex₁!(d, ob₁=dom(para))
  v₂ = add_vertex₂!(d, ob₂=codom(para))
  add_edges!(d, fill(v₁,length(para)), fill(v₂,length(para)), hom=hom(para))
  return d
end

cocone_indices(d::FreeDiagramAsBipartite) = d[:orig_vert₂]
cocone_indices(d::BasicBipartiteFreeDiagram) = parts(d,:V₂)

""" Convert a free diagram to a bipartite free diagram.

Reduce a free diagram to a free bipartite diagram with the same limit (the
default, `colimit=false`) or the same colimit (`colimit=true`). The reduction is
essentially the same in both cases, except for the choice of where to put
isolated vertices, where we follow the conventions described at
[`cone_objects`](@ref) and [`cocone_objects`](@ref). The resulting object is a
bipartite free diagram equipped with maps from the vertices of the bipartite
diagram to the vertices of the original diagram.
"""
function BipartiteFreeDiagram{Ob,Hom}(F::Functor{<:FinCat{Int}};
                                      colimit::Bool=false) where {Ob,Hom}
  d = FreeDiagramAsBipartite{Ob,Hom}()
  g = graph(dom(F))
  add_parts!(d, :V, nv(g))
  for v in vertices(g)
    x = ob_map(F, v)
    out_edges, in_edges = incident(g, v, :src), incident(g, v, :tgt)
    v₁ = if !isempty(out_edges) || (!colimit && isempty(in_edges))
      add_vertex₁!(d, ob₁=x, orig_vert₁=v)
    end
    v₂ = if !isempty(in_edges) || (colimit && isempty(out_edges))
      add_vertex₂!(d, ob₂=x, orig_vert₂=v)
    end
    if !(isnothing(v₁) || isnothing(v₂))
      add_edge!(d, v₁, v₂, hom=id(x))
    end
  end
  for e in edges(g)
    v₁ = only(incident(d, src(g, e), :orig_vert₁))
    v₂ = only(incident(d, tgt(g, e), :orig_vert₂))
    add_edge!(d, v₁, v₂, hom=hom_map(F, e))
  end
  return d
end
BipartiteFreeDiagram(F::Functor{<:FinCat{Int},<:Cat{Ob,Hom}}; kw...) where {Ob,Hom} =
  BipartiteFreeDiagram{Ob,Hom}(F; kw...)

# Free diagrams
#--------------

@present SchFreeDiagram <: SchGraph begin
  Ob::AttrType
  Hom::AttrType
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

@abstract_acset_type AbstractFreeDiagram <: AbstractGraph

@acset_type FreeDiagram(SchFreeDiagram, index=[:src,:tgt]) <:
  AbstractFreeDiagram

ob(d::AbstractFreeDiagram, args...) = subpart(d, args..., :ob)
hom(d::AbstractFreeDiagram, args...) = subpart(d, args..., :hom)

diagram_type(::AbstractFreeDiagram{S,T}) where {S,T<:Tuple} = T

FreeDiagram(obs::AbstractVector{Ob},
            homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(obs, homs)

function FreeDiagram{Ob,Hom}(obs::AbstractVector,
                             homs::AbstractVector) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (f,s,t) in homs)
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  length(homs) > 0 && add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

FreeDiagram(d::FixedShapeFreeDiagram{Ob,Hom}; kw...) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(d; kw...)

function FreeDiagram{Ob,Hom}(discrete::DiscreteDiagram) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(discrete), ob=collect(discrete))
  return d
end

function FreeDiagram{Ob,Hom}(span::Multispan) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  v₀ = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, length(span), ob=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram{Ob,Hom}(cospan::Multicospan) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs = add_vertices!(d, length(cospan), ob=feet(cospan))
  v₀ = add_vertex!(d, ob=apex(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram{Ob,Hom}(para::ParallelMorphisms) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, 2, ob=[dom(para), codom(para)])
  add_edges!(d, fill(1,length(para)), fill(2,length(para)), hom=hom(para))
  return d
end

function FreeDiagram{Ob,Hom}(comp::ComposableMorphisms) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  n = length(comp)
  add_vertices!(d, n+1, ob=[dom.(comp); codom(comp)])
  add_edges!(d, 1:n, 2:(n+1), hom=hom(comp))
  return d
end

function FreeDiagram{Ob,Hom}(diagram::BipartiteFreeDiagram) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs₁ = add_vertices!(d, nv₁(diagram), ob=ob₁(diagram))
  vs₂ = add_vertices!(d, nv₂(diagram), ob=ob₂(diagram))
  add_edges!(d, vs₁[src(diagram)], vs₂[tgt(diagram)], hom=hom(diagram))
  return d
end
FreeDiagram(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(diagram)

function FreeDiagram{Ob,Hom}(F::Functor{<:FinCat{Int}}) where {Ob,Hom}
  J = dom(F)
  js = ob_generators(J)
  js == 1:length(js) || error("Objects must be numbers 1:n")

  diagram = FreeDiagram{Ob,Hom}()
  add_vertices!(diagram, length(js), ob=[ob_map(F,j) for j in js])
  for f in hom_generators(J)
    add_edge!(diagram, dom(J,f), codom(J,f), hom=hom_map(F,f))
  end
  diagram
end
FreeDiagram(F::Functor{<:FinCat{Int},<:Cat{Ob,Hom}}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(F)

(::Type{BFD})(diagram::FreeDiagram; kw...) where BFD <: BipartiteFreeDiagram =
  BFD(FinDomFunctor(diagram); kw...)

# FinDomFunctors as diagrams
#---------------------------

diagram_type(F::FinDomFunctor{Dom,Codom}) where {Ob,Hom,Dom,Codom<:Cat{Ob,Hom}} =
  Tuple{Ob,Hom}
cone_objects(F::FinDomFunctor) = collect_ob(F)
cocone_objects(F::FinDomFunctor) = collect_ob(F)

""" Wrapper type to interpret `FreeDiagram` as a `FinDomFunctor`.
"""
@struct_hash_equal struct FreeDiagramFunctor{Ob,Hom,Codom} <:
    FinDomFunctor{FreeCatGraph{FreeDiagram{Ob,Hom}},Codom}
  diagram::FreeDiagram{Ob,Hom}
  codom::Codom
end
FinDomFunctor(diagram::FreeDiagram, codom::Cat) =
  FreeDiagramFunctor(diagram, codom)
FinDomFunctor(diagram::FreeDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagramFunctor(diagram, TypeCat(Ob, Hom))

dom(F::FreeDiagramFunctor) = FreeCatGraph(F.diagram)

Categories.do_ob_map(F::FreeDiagramFunctor, x) = ob(F.diagram, x)
Categories.do_hom_map(F::FreeDiagramFunctor, f) = hom(F.diagram, f)

collect_ob(F::FreeDiagramFunctor) = ob(F.diagram)
collect_hom(F::FreeDiagramFunctor) = hom(F.diagram)

end

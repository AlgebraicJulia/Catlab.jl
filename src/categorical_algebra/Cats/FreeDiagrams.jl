module FreeDiagrams 

export Diagram, EmptyDiagram,SingletonDiagram, ObjectPair, DiscreteDiagram, 
       ComposablePair, ComposableMorphisms, cocone_objects,
       Multispan, Multicospan, ParallelPair, cone_objects, 
       ParallelMorphisms, BipartiteFreeDiagram, apex, legs, feet, Span, Cospan, getcategory,
       FreeDiagram, ob₁, ob₂, AbsBipartiteFreeDiagram, specialize

using StructEquality
using StaticArrays: StaticVector, SVector

using GATlab, ACSets
import ACSets: objects

import ....Theories: ob, dom, codom, hom
using ....BasicSets: FinSet
import ....BasicSets.Sets: left, right
using ....Graphs
import ....Graphs: add_vertices!, add_vertices₁!, add_vertices₂!, nv, ne, nv₁, nv₂, 
  vertices, vertices₁, vertices₂, edges, src, tgt, rem_vertices₂!,
  add_vertex!, add_vertex₁!, add_vertex₂!, add_edge!, add_edges!,
  inneighbors, rem_edges!

using ..Categories: Category
import ..Categories: obtype, homtype, FreeCatGraph, get_ob, get_hom, get_ob_set, get_hom_set

"""
Some collection of objects and morphisms (which could be interpreted as living 
in some category, though subtypes of this needn't specify which category). 

Some diagrams can be interpreted as (co)limit diagrams. These ought implement a
(co)cone_objects method.
"""
abstract type DiagramImpl end

"""
A diagram in a category 
"""
@struct_hash_equal struct Diagram
  impl::DiagramImpl
  cat::Category
end 

GATlab.getvalue(d::Diagram) = d.impl

getcategory(d::Diagram) = d.cat

obtype(d::Diagram) = obtype(category(d))

homtype(d::Diagram) = homtype(category(d))

cone_objects(d::Diagram) = cone_objects(getvalue(d))

cocone_objects(d::Diagram) = cocone_objects(getvalue(d))

""" Default diagram, given just a model of `ThCategory` """
Diagram(m::Category) = Diagram(EmptyDiagram{obtype(m)}(), m)

# Discrete
##########

""" Discrete diagram: a diagram with no non-identity morphisms.
"""
@struct_hash_equal struct DiscreteDiagram{Ob,Obs<:AbstractVector{Ob}
                                         } <: DiagramImpl
  objects::Obs
end

DiscreteDiagram{Ob}(o::Obs) where {Ob,Obs<:AbstractVector{Ob}} = 
  DiscreteDiagram{Ob,Obs}(o)

cone_objects(d::DiscreteDiagram) = d.objects

cocone_objects(d::DiscreteDiagram) = d.objects

objects(d::DiscreteDiagram) = d.objects

Base.length(m::DiscreteDiagram) = length(m.objects) 

Base.iterate(m::DiscreteDiagram, x...) = iterate(m.objects, x...)

Base.eltype(d::DiscreteDiagram) = eltype(d.objects)

Base.getindex(d::DiscreteDiagram, i) = d.objects[i]

Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)

Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

obtype(::DiscreteDiagram{Ob}) where Ob = Ob

# Special subtypes
#-----------------

const EmptyDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{0,Ob}}

EmptyDiagram{Ob}() where Ob = DiscreteDiagram(SVector{0,Ob}())

const SingletonDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{1,Ob}}

SingletonDiagram(ob) = DiscreteDiagram(SVector(ob))

const ObjectPair{Ob} = DiscreteDiagram{Ob,<:StaticVector{2,Ob}}

ObjectPair(first, second) = DiscreteDiagram(SVector(first, second))

# Co)spans
##################

# Generic code to both (multi)(co)spans 
#--------------------------------------
abstract type Multi_Co_Span <: DiagramImpl end

apex(m::Multi_Co_Span) = m.apex

Base.length(m::Multi_Co_Span) = length(legs(m)) 

Base.iterate(m::Multi_Co_Span, x...) = iterate(legs(m), x...)

# Generic code to both spans and cospans 
#---------------------------------------

abstract type SpanCospan <: Multi_Co_Span end

legs(m::SpanCospan) = [left(m), right(m)]

left(s::SpanCospan) = s.left 

right(s::SpanCospan) = s.right 

objects(s::Multi_Co_Span) = [apex(s), feet(s)...]

# Spans 
#-----------

@struct_hash_equal struct Span{Ob, Hom} <: SpanCospan
  apex::Ob
  left::Hom
  right::Hom
  function Span{Ob, Hom}(f, g) where {Ob, Hom}
    dom(f) == dom(g) || error("Cannot make span from $f and $g") 
    new{Ob,Hom}(dom(f), f, g)
  end
end

obtype(::Span{Ob}) where Ob = Ob

homtype(::Span{<:Any,Hom}) where Hom = Hom


Span(f::Hom, g::Hom) where Hom = Span{typeof(dom(f)),Hom}(f, g)

feet(m::Span) = codom.(legs(m))

""" We naturally take colimits of spans, but not limits """
cocone_objects(span::Span) = feet(span)

# Cospans
#--------

@struct_hash_equal struct Cospan{Ob, Hom} <: SpanCospan
  apex::Ob
  left::Hom
  right::Hom
  function Cospan{Ob, Hom}(f, g) where {Ob, Hom}
    codom(f) == codom(g) || error("Cannot make cospan from $f and $g") 
    new{Ob,Hom}(codom(f), f, g)
  end
end


obtype(::Cospan{Ob}) where Ob = Ob

homtype(::Cospan{<:Any,Hom}) where Hom = Hom

Cospan(f::Hom, g::Hom) where Hom = Cospan{typeof(dom(f)),Hom}(f, g)

feet(m::Cospan) = dom.(legs(m))

""" We naturally take limits of cospans, but not colimits """
cone_objects(cospan::Cospan) = feet(cospan)

# Multi(co)spans
##################

# Generic code to both multispans and multicospans 
#-------------------------------------------------

abstract type MultiSpanCospan <: Multi_Co_Span end

legs(m::MultiSpanCospan) = m.legs

function left(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  first(legs(s))
end

function right(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  last(legs(s))
end

# Multispans 
#-----------

@struct_hash_equal struct Multispan{Ob, Hom} <: MultiSpanCospan
  apex::Ob
  legs::AbstractVector{Hom}
  function Multispan{Ob, Hom}(apex,legs) where {Ob,Hom}
    all([dom(l)==apex for l in legs]) || error("Bad span")
    new{Ob,Hom}(apex, legs)
  end
end


obtype(::Multispan{Ob}) where Ob = Ob

homtype(::Multispan{Any,Hom}) where Hom = Hom

""" infer types """
Multispan(apex::Ob,legs::AbstractVector{Hom}) where {Ob,Hom} = 
  Multispan{Ob,Hom}(apex, legs)

""" Construct from just a list, assuming it's nonempty """
Multispan(legs::AbstractVector) = Multispan(dom(first(legs)), legs)

""" Cast a span to a Multispan """
Multispan(s::Span{Ob,Hom}) where {Ob, Hom} = Multispan{Ob,Hom}(apex(s), legs(s))

""" Empty span """
Multispan{Ob, Hom}(a::Ob) where {Ob, Hom} = Multispan{Ob, Hom}(a, Hom[])


function Multispan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multispan needs an apex")   
  allequal(dom.(hs)) || error("Span domains not equal")
  Multispan{Ob, Hom}(dom(first(hs)), hs)
end

feet(m::Multispan) = codom.(legs(m))

cocone_objects(span::Multispan) = feet(span)

# Multicospans 
#-------------

@struct_hash_equal struct Multicospan{Ob, Hom} <: MultiSpanCospan
  apex::Ob
  legs::AbstractVector{Hom}
  function Multicospan{Ob, Hom}(apex,legs) where {Ob,Hom}
    all([codom(l)==apex for l in legs]) || error("Bad cospan")
    new{Ob,Hom}(apex, legs)
  end
end

obtype(::Multicospan{Ob}) where Ob = Ob

homtype(::Multicospan{Any,Hom}) where Hom = Hom

""" infer types """
Multicospan(apex::Ob,legs::AbstractVector{Hom}) where {Ob,Hom} = 
  Multicospan{Ob,Hom}(apex, legs)

""" Construct from just a list, assuming it's nonempty """
Multicospan(legs::AbstractVector) = Multicospan(codom(first(legs)), legs)


""" Cast a cospan to a Multicospan """
Multicospan(s::Cospan{Ob,Hom}) where {Ob, Hom} = 
  Multicospan{Ob,Hom}(apex(s), legs(s))

""" Empty cospan """
Multicospan{Ob, Hom}(a::Ob) where {Ob, Hom}= Multicospan{Ob, Hom}(a, Hom[])

function Multicospan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multicospan needs an apex")   
  allequal(codom.(hs)) || error("Cospan codomains not equal")
  Multicospan{Ob, Hom}(codom(first(hs)), hs)
end

feet(m::Multicospan) = dom.(legs(m))

cone_objects(cospan::Multicospan) = feet(cospan)

# Parallel morphisms
####################

@struct_hash_equal struct ParallelMorphisms{Ob, Hom, Homs<:AbstractVector{Hom}
                                            } <: DiagramImpl
  dom::Ob
  codom::Ob
  homs::Homs
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Ob,Hom} = ParallelMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

Base.length(m::ParallelMorphisms) = length(m.homs) 

Base.iterate(m::ParallelMorphisms, x...) = iterate(m.homs, x...)

Base.getindex(m::ParallelMorphisms, x) = m.homs[x]

Base.lastindex(m::ParallelMorphisms) = lastindex(m.homs)

dom(p::ParallelMorphisms) = p.dom

codom(p::ParallelMorphisms) = p.codom

hom(comp::ParallelMorphisms) = comp.homs

objects(p::ParallelMorphisms) = [dom(p), codom(p)]

cone_objects(para::ParallelMorphisms) = SVector(dom(para))

cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

function ParallelMorphisms(xs::Hs) where {H, Hs<:AbstractVector{H}}
  isempty(xs) && error("Parallel morphisms must be nonempty")
  allequal(dom.(xs)) || error("Parallel morphism must share domain")
  allequal(codom.(xs)) || error("Parallel morphism must share domain")
  d, c = dom(first(xs)), codom(first(xs))
  Ob = Union{typeof(d), typeof(c)}
  ParallelMorphisms{Ob,H,Hs}(d, c, xs)
end

function ParallelPair(first, last)
  ParallelMorphisms(SVector(first, last))
end


# Composable morphisms
#---------------------

""" Composable morphisms in a category.

Composable morphisms are a sequence of morphisms in a category that form a path
in the underlying graph of the category.

For the common special case of two morphisms, see [`ComposablePair`](@ref).
"""
@struct_hash_equal struct ComposableMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}
                                             } <: DiagramImpl
  homs::Homs
end

""" Infer types """
function ComposableMorphisms(homs::AbstractVector{Hom}) where Hom
  Ob = Union{typeof.([dom.(homs); codom(last(homs))])...}
  ComposableMorphisms{Ob, Hom}(homs)
end

function ComposableMorphisms{Ob,Hom}(homs::Homs) where {Ob, Hom, Homs<:AbstractVector{Hom}}
  isempty(homs) && error("Composable morphisms must be nonempty")
  doms, codoms = dom.(homs), codom.(homs)
  all(x -> x isa Ob, doms) || error("Not all doms are $Ob")
  last(codoms) isa Ob || error("Not all codoms are $Ob")
  all(c == d for (c,d) in zip(codoms[1:end-1], doms[2:end])) || error(
    "Domain mismatch in composable sequence: $homs")
  ComposableMorphisms{Ob,Hom,Homs}(homs)
end

dom(comp::ComposableMorphisms) = dom(first(comp))

codom(comp::ComposableMorphisms) = codom(last(comp))

hom(comp::ComposableMorphisms) = comp.homs

Base.iterate(comp::ComposableMorphisms, args...) = iterate(comp.homs, args...)

Base.eltype(comp::ComposableMorphisms) = eltype(comp.homs)

Base.length(comp::ComposableMorphisms) = length(comp.homs)

Base.getindex(comp::ComposableMorphisms, i) = comp.homs[i]

Base.firstindex(comp::ComposableMorphisms) = firstindex(comp.homs)

Base.lastindex(comp::ComposableMorphisms) = lastindex(comp.homs)

objects(p::ComposableMorphisms) = [dom(p), codom.(hom(p))...]

""" Pair of composable morphisms in a category.

[Composable pairs](https://ncatlab.org/nlab/show/composable+pair) are a common
special case of [`ComposableMorphisms`](@ref).
"""
const ComposablePair{Ob,Hom} = ComposableMorphisms{Ob,Hom,<:StaticVector{2,Hom}}


# Constructor in which we infer Hom and Ob type
ComposablePair(f::Hom, g::Hom) where Hom = ComposablePair{Hom}(f, g)

# Constructor in which we infer Ob type
function ComposablePair{Hom}(first::Hom, last::Hom) where Hom
  Ob = Union{typeof.([dom(first), dom(last), codom(last)])...}
  ComposableMorphisms{Ob, Hom}(SVector(first, last))
end

# Diagrams of flexible shape
############################
abstract type ACSetWrapper{Ob,Hom} <: DiagramImpl end

GATlab.getvalue(b::ACSetWrapper) = b.val

ob(d::ACSetWrapper, args...) = subpart(getvalue(d), args..., :ob)

ob₁(d::ACSetWrapper, args...) = subpart(getvalue(d), args..., :ob₁)

ob₂(d::ACSetWrapper, args...) = subpart(getvalue(d), args..., :ob₂)

hom(d::ACSetWrapper, args...) = subpart(getvalue(d), args..., :hom)

ACSets.incident(d::ACSetWrapper, args...) = incident(getvalue(d), args...)

ACSets.copy_parts!(d::ACSetWrapper, e::ACSetWrapper, args...; kw...) = 
  copy_parts!(getvalue(d), getvalue(e), args...; kw...)

src(d::ACSetWrapper, args...) = src(getvalue(d), args...)

tgt(d::ACSetWrapper, args...) = tgt(getvalue(d), args...)

add_vertices₁!(d::ACSetWrapper, x...; kw...) = add_vertices₁!(getvalue(d), x...; kw...)

add_vertices₂!(d::ACSetWrapper, x...; kw...) = add_vertices₂!(getvalue(d), x...; kw...)

nv(d::ACSetWrapper) = nv(getvalue(d)) 

ne(d::ACSetWrapper) = ne(getvalue(d)) 

nv₁(d::ACSetWrapper) = nv₁(getvalue(d)) 

nv₂(d::ACSetWrapper) = nv₂(getvalue(d)) 

vertices₁(d::ACSetWrapper) = vertices₁(getvalue(d)) 

vertices₂(d::ACSetWrapper) = vertices₂(getvalue(d)) 

edges(d::ACSetWrapper) = edges(getvalue(d))

add_vertex₁!(d::ACSetWrapper; kw...) = add_vertex₁!(getvalue(d); kw...) 

add_vertex₂!(d::ACSetWrapper; kw...) = add_vertex₂!(getvalue(d); kw...) 

add_edge!(d::ACSetWrapper, args...; kw...) = add_edge!(getvalue(d), args...; kw...)

add_edges!(d::ACSetWrapper, args...; kw...) = add_edges!(getvalue(d), args...; kw...)

vertices(d::ACSetWrapper) = vertices(getvalue(d)) 

add_vertices!(d::ACSetWrapper, arg...; kw...) = 
  add_vertices!(getvalue(d), arg...; kw...) 

add_vertex!(d::ACSetWrapper; kw...) = add_vertex!(getvalue(d); kw...) 

rem_vertices₂!(d::ACSetWrapper, args...) = rem_vertices₂!(getvalue(d), args...)

rem_edges!(d::ACSetWrapper, args...) = rem_edges!(getvalue(d), args...)

inneighbors(d::ACSetWrapper, args...) = inneighbors(getvalue(d), args...)

# Bipartite free diagrams
#------------------------

@abstract_acset_type _BipartiteFreeDiagram <: AbstractUndirectedBipartiteGraph

@present SchBipartiteFreeDiagram <: SchUndirectedBipartiteGraph begin
  (Ob, Hom)::AttrType
  ob₁::Attr(V₁, Ob)
  ob₂::Attr(V₂, Ob)
  hom::Attr(E, Hom)
end

@present SchFreeDiagramAsBipartite <: SchBipartiteFreeDiagram begin
  V::Ob
  orig_vert₁::Hom(V₁, V)
  orig_vert₂::Hom(V₂, V)
end

""" The default concrete type for bipartite free diagrams. """
@acset_type BasicBipartiteFreeDiagram(SchBipartiteFreeDiagram,
  index=[:src, :tgt]) <: _BipartiteFreeDiagram

@acset_type _FreeDiagramAsBipartite(SchFreeDiagramAsBipartite,
  index=[:src, :tgt], unique_index=[:orig_vert₁, :orig_vert₂]) <: _BipartiteFreeDiagram

abstract type AbsBipartiteFreeDiagram{Ob,Hom} <: ACSetWrapper{Ob,Hom} end

cone_objects(diagram::AbsBipartiteFreeDiagram) = ob₁(diagram)

cocone_objects(diagram::AbsBipartiteFreeDiagram) = ob₂(diagram)

objects(diagram::AbsBipartiteFreeDiagram) = [ob₁(diagram)..., ob₂(diagram)...]

""" A free diagram with a bipartite structure.

Such diagrams include most of the fixed shapes, such as spans, cospans, and
parallel morphisms. They are also the generic shape of diagrams for limits and
colimits arising from undirected wiring diagrams. For limits, the boxes
correspond to vertices in ``V₁`` and the junctions to vertices in ``V₂``.
Colimits are dual.
"""
@struct_hash_equal struct BipartiteFreeDiagram{Ob, Hom} <: AbsBipartiteFreeDiagram{Ob,Hom}
  val::BasicBipartiteFreeDiagram{Ob,Hom}
end

BipartiteFreeDiagram{Ob,Hom}() where {Ob,Hom} =
  BipartiteFreeDiagram(BasicBipartiteFreeDiagram{Ob,Hom}())

cocone_indices(d::BasicBipartiteFreeDiagram) = parts(getvalue(d), :V₂)  

Base.map(b::BasicBipartiteFreeDiagram, args...; kw...) = 
  BasicBipartiteFreeDiagram(map(getvalue(b), args...; kw...))


""" A free diagram that has been converted to a bipartite free diagram.
"""
@struct_hash_equal struct FreeDiagramAsBipartite{Ob, Hom} <: AbsBipartiteFreeDiagram{Ob,Hom}
  val::_FreeDiagramAsBipartite{Ob,Hom}
end

FreeDiagramAsBipartite{Ob, Hom}() where {Ob, Hom} =
  FreeDiagramAsBipartite{Ob, Hom}(_FreeDiagramAsBipartite{Ob,Hom}())

cocone_indices(d::FreeDiagramAsBipartite) = getvalue(d)[:orig_vert₂]

Base.map(b::FreeDiagramAsBipartite, args...; kw...) = 
  FreeDiagramAsBipartite(map(getvalue(b), args...; kw...))

# Cast other diagram types to bipartite free diagrams 
#----------------------------------------------------

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

function BipartiteFreeDiagram(discrete::DiscreteDiagram{Ob,Hom};
                                      colimit::Bool=false) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  if colimit
    add_vertices₂!(d, length(discrete), ob₂=collect(discrete))
  else
    add_vertices₁!(d, length(discrete), ob₁=collect(discrete))
  end
  return d
end

BipartiteFreeDiagram(span::Span) = BipartiteFreeDiagram(Multispan(span))

BipartiteFreeDiagram(cospan::Cospan) = BipartiteFreeDiagram(Multicospan(cospan))

function BipartiteFreeDiagram(span::Multispan{Ob,Hom}) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₁!(d, ob₁=apex(span))
  vs = add_vertices₂!(d, length(span), ob₂=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function BipartiteFreeDiagram(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₂!(d, ob₂=apex(cospan))
  vs = add_vertices₁!(d, length(cospan), ob₁=feet(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function BipartiteFreeDiagram(para::ParallelMorphisms{Ob,Hom}) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₁ = add_vertex₁!(d, ob₁=dom(para))
  v₂ = add_vertex₂!(d, ob₂=codom(para))
  add_edges!(d, fill(v₁,length(para)), fill(v₂,length(para)), hom=hom(para))
  return d
end


""" Try to find a more specific DiagramImpl for a BipartiteFreeDiagram """
function specialize(d::AbsBipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  N = sum(nv(d))
  N == 0 && return EmptyDiagram{Ob}(Hom)
  if ne(d) == 0 
    N == 1 && return SingletonDiagram(only(objects(d)))
    N == 2 && return ObjectPair(objects(d)...)
    return DiscreteDiagram([ob₁(d); ob₂(d)])
  end
  eqd = allequal(dom.(hom(d)))
  eqc = allequal(codom.(hom(d)))
  eqd && eqc && return ParallelMorphisms{Ob,Hom}(hom(d)) # covers ne=1 case
  eqd && return (ne(d) == 2 ? Span{Ob,Hom} : Multispan{Ob,Hom})(hom(d))
  eqc && return (ne(d) == 2 ? Cospan{Ob,Hom} : Multicospan{Ob,Hom})(hom(d))
  d
end

# Cast to other diagram types from bipartite free diagrams (can fail)
#--------------------------------------------------------------------

Multispan(d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} = 
  Multispan{Ob,Hom}(only(ob₁(d)), hom(d))

Multicospan(d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} = 
  Multicospan{Ob,Hom}(only(ob₂(d)), hom(d))

# Free diagrams
#--------------

@present SchFreeDiagram <: SchGraph begin
  (Ob, Hom)::AttrType
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

@abstract_acset_type AbstractFreeDiagram <: AbstractGraph

@acset_type _FreeDiagram(SchFreeDiagram, index=[:src,:tgt]) <: AbstractFreeDiagram

@struct_hash_equal struct FreeDiagram{Ob,Hom} <: ACSetWrapper{Ob,Hom}
  val::AbstractFreeDiagram{<:Any, Tuple{Ob,Hom}} 
end 

GATlab.getvalue(f::FreeDiagram) = f.val

FreeDiagram{Ob, Hom}() where {Ob, Hom} = FreeDiagram{Ob,Hom}(_FreeDiagram{Ob,Hom}())

objects(f::FreeDiagram) = ob(f)

""" Infer types """
FreeDiagram(obs::AbstractVector{Ob},homs::AbstractVector{Tuple{Hom,Int,Int}}
           ) where {Ob,Hom} = FreeDiagram{Ob,Hom}(obs, homs)

function FreeDiagram{Ob,Hom}(obs::AbstractVector,
                             homs::AbstractVector) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (f,s,t) in homs)
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  length(homs) > 0 && add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

function FreeDiagram{Ob,Hom}(discrete::DiscreteDiagram) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(discrete), ob=collect(discrete))
  return d
end

FreeDiagram{Ob,Hom}(span::Span) where {Ob,Hom} = 
  FreeDiagram{Ob,Hom}(Multispan(span))

function FreeDiagram{Ob,Hom}(span::Multispan) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  v₀ = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, length(span), ob=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

FreeDiagram{Ob,Hom}(cospan::Cospan) where {Ob,Hom} = 
  FreeDiagram{Ob,Hom}(Multicospan(cospan))

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

FreeDiagram(diagram::DiscreteDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(BipartiteFreeDiagram(diagram))

FreeDiagram(diagram::ParallelMorphisms{Ob,Hom}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(BipartiteFreeDiagram(diagram))

function FreeDiagram(comp::ComposableMorphisms{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  n = length(comp)
  add_vertices!(d, n+1, ob=[dom.(comp); codom(comp)])
  add_edges!(d, 1:n, 2:(n+1), hom=hom(comp))
  return d
end
  

FreeDiagram(diagram::Multi_Co_Span) =
  FreeDiagram{obtype(diagram),homtype(diagram)}(diagram)

FreeDiagram(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(diagram)

FreeDiagram(f::FreeDiagram) = f

# FreeCatGraph interface 
# TODO POSSIBLY DELETE ALL THIS
FreeCatGraph(n::FreeDiagram) =  FreeCatGraph(getvalue(n))

# get_ob(g::_FreeDiagram, x) = g[x, :ob]
# get_hom(g::_FreeDiagram, x) = g[x, :hom] 
# get_ob_set(g::_FreeDiagram) = FinSet(Set(g[:ob]))
# get_hom_set(g::_FreeDiagram) = FinSet(Set(g[:hom]))


""" Convert a free diagram to a bipartite free diagram.

Reduce a free diagram to a free bipartite diagram with the same limit (the
default, `colimit=false`) or the same colimit (`colimit=true`). The reduction is
essentially the same in both cases, except for the choice of where to put
isolated vertices, where we follow the conventions described at
[`cone_objects`](@ref) and [`cocone_objects`](@ref). The resulting object is a
bipartite free diagram equipped with maps from the vertices of the bipartite
diagram to the vertices of the original diagram.
"""
function BipartiteFreeDiagram{Ob,Hom}(g::FreeDiagram;
                                      colimit::Bool=false) where {Ob,Hom}
  d = FreeDiagramAsBipartite{Ob,Hom}()
  add_parts!(getvalue(d), :V, nv(g))
  for v in vertices(g)
    x = ob(g, v)
    out_edges, in_edges = incident(g, v, :src), incident(g, v, :tgt)
    v₁ = if !isempty(out_edges) || (!colimit && isempty(in_edges))
      add_vertex₁!(d, ob₁=x, orig_vert₁=v)
    end
    v₂ = if !isempty(in_edges) || (colimit && isempty(out_edges))
      add_vertex₂!(d, ob₂=x, orig_vert₂=v)
    end
    if !(isnothing(v₁) || isnothing(v₂))
      add_edge!(getvalue(d), v₁, v₂, hom=id(x))
    end
  end
  for e in edges(g)
    v₁ = only(incident(d, src(g, e), :orig_vert₁))
    v₂ = only(incident(d, tgt(g, e), :orig_vert₂))
    add_edge!(getvalue(d), v₁, v₂, hom=hom(g, e))
  end
  return d
end

BipartiteFreeDiagram(g::FreeDiagram{Ob,Hom}; kw...) where {Ob, Hom} = 
  BipartiteFreeDiagram{Ob,Hom}(g; kw...)

""" Try to find a more specific DiagramImpl for a FreeDiagram """
function specialize(d::FreeDiagram{Ob,Hom}; colimit=false) where {Ob,Hom}
  specialize(BipartiteFreeDiagram{Ob,Hom}(d; colimit))
end

end # module 

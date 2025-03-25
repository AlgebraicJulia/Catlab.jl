export Diagram, SimpleDiagram, DiagramHom, id, op, co,
  shape, diagram, shape_map, diagram_map

using StructEquality

using GATlab
import ....Theories: dom, codom, id, compose, ⋅, ∘, munit
using ....Theories: ThCategory, composeH, FreeSchema
import ....BasicSets: FinDomFunction
using ...Cats
import ..Functors: ob_map, hom_map, op
import ..FinFunctors: force, collect_ob, collect_hom
import ..Transformations: co
import ..LimitsColimits: limit, colimit, universal

# Data types
############

""" Diagram in a category.

Recall that a *diagram* in a category ``C`` is a functor ``D: J → C``, where for
us the *shape category* ``J`` is finitely presented. Although such a diagram is
captured perfectly well by a `FinDomFunctor`, there are several different
notions of morphism between diagrams. The first type parameter `T` in this
wrapper type distinguishes which diagram category the diagram belongs to. See
[`DiagramHom`](@ref) for more about the possible choices. The parameter `T` may
also be `Any` to indicate that no choice has (yet) been made.
"""
abstract type Diagram{T,C<:Cat,D<:FinDomFunctor} end
Diagram(args...) = Diagram{Any}(args...)

# The first type parameter is considered part of the data!
Base.hash(d::Diagram{T}, h::UInt) where T = hash(T, struct_hash(d, h))
Base.:(==)(d1::Diagram{T}, d2::Diagram{S}) where {T,S} =
  T == S && struct_equal(d1, d2)

""" Default concrete type for diagram in a category.
"""
struct SimpleDiagram{T,C<:Cat,D<:Functor{<:FinCat,C}} <: Diagram{T,C,D}
  diagram::D
end
SimpleDiagram{T}(F::D) where {T,C<:Cat,D<:Functor{<:FinCat,C}} =
  SimpleDiagram{T,C,D}(F)
SimpleDiagram{T}(d::SimpleDiagram) where T = SimpleDiagram{T}(d.diagram)

Diagram{T}(F::Union{Functor,SimpleDiagram}) where T = SimpleDiagram{T}(F)

function Base.show(io::IO, d::SimpleDiagram{T}) where T
  print(io, "Diagram{$T}(")
  show(io, diagram(d))
  print(io, ")")
end

"""
Force-evaluate the functor in a diagram.
"""
force(d::SimpleDiagram{T}, args...) where T =
  SimpleDiagram{T}(force(diagram(d), args...))

""" Functor underlying a diagram in a category.
"""
diagram(d::Diagram) = d.diagram
"""Functor underlying a diagram in a category."""
functor(d::Diagram) = d.diagram

""" The *shape* or *indexing category* of a diagram.

This is the domain of the underlying functor.
"""
shape(d::Diagram) = dom(diagram(d))

ob_map(d::Diagram, x) = ob_map(diagram(d), x)
hom_map(d::Diagram, f) = hom_map(diagram(d), f)
collect_ob(d::Diagram) = collect_ob(diagram(d))
collect_hom(d::Diagram) = collect_hom(diagram(d))

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
type `DiagramHom{id}` and `DiagramHom{op}` induce morphisms between colimits and
between limits of the diagrams, respectively, whereas morphisms of type
`DiagramHom{co}` generalize morphisms of polynomial functors.
"""
abstract type DiagramHom{T,C<:Cat} end

struct SimpleDiagramHom{T,C<:Cat,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C}}<:DiagramHom{T,C}
  shape_map::F
  diagram_map::Φ # bug: Φ should be type constrained to be a FinTransformation  
  precomposed_diagram::D
end


DiagramHom{T}(shape_map::F, diagram_map::Φ, precomposed_diagram::D) where
    {T,C,F<:FinFunctor,Φ<:FinTransformation,D<:Functor{<:FinCat,C}} =
    SimpleDiagramHom{T,C,F,Φ,D}(shape_map, diagram_map, precomposed_diagram) 
"""Convert the diagram category in which a diagram hom is being viewed."""
DiagramHom{T}(f::DiagramHom) where T =
  DiagramHom{T}(f.shape_map, f.diagram_map, f.precomposed_diagram)

DiagramHom{T}(ob_maps, hom_map, D::Diagram{T}, D′::Diagram{T};kw...) where T =
  DiagramHom{T}(ob_maps, hom_map, diagram(D), diagram(D′);kw...)
DiagramHom{T}(ob_maps, D::Union{Diagram{T},FinDomFunctor},
              D′::Union{Diagram{T},FinDomFunctor};kw...) where T =
  DiagramHom{T}(ob_maps, nothing, D, D′;kw...)

function DiagramHom{T}(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor;kw...) where T
  f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′))
  DiagramHom{T}(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′;kw...)
end
function DiagramHom{op}(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor;kw...)
  f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D′), dom(D))
  DiagramHom{op}(f, mapvals(x -> cell2(D,x), ob_maps), D, D′;kw...)
end

function DiagramHom{id}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor;kw...)
  ϕ = FinTransformation(components, D, f⋅D′)
  DiagramHom{id}(f, ϕ, D′;kw...)
end
function DiagramHom{op}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor;kw...)
  ϕ = FinTransformation(components, f⋅D, D′)
  DiagramHom{op}(f, ϕ, D;kw...)
end
function DiagramHom{co}(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor;kw...)
  ϕ = FinTransformation(components, f⋅D′, D)
  DiagramHom{co}(f, ϕ, D′;kw...)
end

cell1(pair::Union{Pair,Tuple{Any,Any}}) = first(pair)
cell1(x) = x
cell2(D::FinDomFunctor, pair::Union{Pair,Tuple{Any,Any}}) = last(pair)
cell2(D::FinDomFunctor, x) = id(codom(D), ob_map(D, x))

shape_map(f::DiagramHom) = f.shape_map
diagram_map(f::DiagramHom) = f.diagram_map

Base.hash(f::DiagramHom{T}, h::UInt) where {T} = hash(T, struct_hash(f, h))

Base.:(==)(f::DiagramHom{T}, g::DiagramHom{S}) where {T,S} =
  T == S && struct_equal(f, g)

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

@instance ThCategory{Diagram,DiagramHom} begin
  @import dom, codom, compose, id
end

# Oppositization 2-functor induces isomorphisms of diagram categories:
#    op(Diag{id}(C)) ≅ Diag{op}(op(C))
#    op(Diag{op}(C)) ≅ Diag{id}(op(C))

op(d::Diagram{Any}) = Diagram{Any}(op(diagram(d)))
op(d::Diagram{id}) = Diagram{op}(op(diagram(d)))
op(d::Diagram{op}) = Diagram{id}(op(diagram(d)))
op(f::DiagramHom{id}) = DiagramHom{op}(op(shape_map(f)), op(diagram_map(f)),
                                       op(f.precomposed_diagram))
op(f::DiagramHom{op}) = DiagramHom{id}(op(shape_map(f)), op(diagram_map(f)),
                                       op(f.precomposed_diagram))

# Any functor ``F: C → D`` induces a functor ``Diag(F): Diag(C) → Diag(D)`` by
# post-composition and post-whiskering.
function compose(d::Diagram{T}, F::Functor; kw...) where T
  Diagram{T}(compose(diagram(d), F; kw...))
end
function compose(f::DiagramHom{T}, F::Functor; kw...) where T
  whiskered = composeH(diagram_map(f), F; kw...)
  DiagramHom{T}(shape_map(f), whiskered,
                compose(f.precomposed_diagram, F; kw...))
end

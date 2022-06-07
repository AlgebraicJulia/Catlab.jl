""" Diagrams in a category and their morphisms.
"""
module Diagrams
export Diagram, DiagramHom, id, op, co, shape, diagram, shape_map, diagram_map

using ...GAT
import ...Theories: dom, codom, id, compose, ⋅, ∘, munit
using ...Theories: Category, composeH
import ..Categories: ob_map, hom_map, op, co
using ..FinCats, ..FreeDiagrams
using ..FinCats: mapvals
import ..FinCats: force, collect_ob, collect_hom
import ..Limits: limit, colimit, universal

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

collect_ob(d::Diagram) = collect_ob(diagram(d))
collect_hom(d::Diagram) = collect_hom(diagram(d))

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

# Oppositization 2-functor induces isomorphisms of diagram categories:
#    op(Diag{id}(C)) ≅ Diag{op}(op(C))
#    op(Diag{op}(C)) ≅ Diag{id}(op(C))

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

end

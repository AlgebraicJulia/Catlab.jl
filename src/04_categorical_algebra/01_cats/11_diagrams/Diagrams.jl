export Diagram, SimpleDiagram, DiagramHom, id, op, co,
  shape, diagram, shape_map, diagram_map

using StructEquality
using GATlab

import ....Theories: dom, codom, id, compose, ⋅, ∘
using ..FinCats, ..FreeDiagrams
using ..FinFunctors: mapvals, FinFunctor, FinDomFunctor
import ..FinFunctors: collect_ob, collect_hom
using ..NatTrans: Transformation

# Morphisms of diagrams
#######################

@struct_hash_equal struct DiagramHom 
  shape_map::FinFunctor
  diagram_map::Transformation
  precomposed_diagram::FinFunctor
end

# Accessors
#----------
shape_map(f::DiagramHom) = f.shape_map
diagram_map(f::DiagramHom) = f.diagram_map

# Other methods
#--------------

# function Base.show(io::IO, f::DiagramHom)
#   J = dom(shape_map(f))
#   print(io, "DiagramHom([")
#   join(io, mapvals(x -> ob_map(f,x), ob_generators(J), iter=true), ", ")
#   print(io, "], [")
#   join(io, mapvals(g -> hom_map(f,g), hom_generators(J), iter=true), ", ")
#   print(io, "], ")
#   show(IOContext(io, :compact=>true, :hide_domains=>true), diagram(dom(f)))
#   print(io, ", ")
#   show(IOContext(io, :compact=>true, :hide_domains=>true), diagram(codom(f)))
#   print(io, ")")
# end

""" The *shape* or *indexing category* of a diagram.

This is the domain of the functor.
"""
shape(d::FinDomFunctor) = dom(d)

ob_map(f::DiagramHom, x) = (ob_map(f.shape_map, x), component(f.diagram_map, x))

hom_map(f::DiagramHom, g) = hom_map(f.shape_map, g)

collect_ob(f::DiagramHom) =
  collect(zip(collect_ob(f.shape_map), components(f.diagram_map)))

collect_hom(f::DiagramHom) = collect_hom(f.shape_map)

##########################
# Categories of diagrams #
##########################

""" Diagram in a category.

Recall that a *diagram* in a category ``C`` is a functor ``D: J → C``, where for
us the *shape category* ``J`` is finitely presented. There are several different
notions of morphism from a diagram ``D: J → C`` to another diagram 
``D′: J′ → C``:

1. `Diagram`: a functor ``F: J → J′`` together with a natural
   transformation ``ϕ: D ⇒ F⋅D′``
2. `DiagramOp`: a functor ``F: J′ → J`` together with a natural
   transformation ``ϕ: F⋅D ⇒ D′``
3. `DiagramCo`: a functor ``F: J → J′`` together with a natural
   transformation ``ϕ: F⋅D′ ⇒ D``.

Note that `DiagramOp` is *not* the opposite category of `Diagram`, but
`DiagramOp` and `DiagramCo` are opposites of each other. Explicit support is
included for both because they are useful for different purposes: morphisms of
type `DiagramHom` and `DiagramHomOp` induce morphisms between colimits and
between limits of the diagrams, respectively, whereas morphisms of type
`DiagramHomCo` generalize morphisms of polynomial functors.
"""
abstract type DiagramCat end 

@struct_hash_equal struct Diagram <: DiagramCat end

@struct_hash_equal struct DiagramOp <: DiagramCat end

@struct_hash_equal struct DiagramCo <: DiagramCat end

# Constructors
##############

DiagramHom(ob_maps, D::FinDomFunctor, D′::FinDomFunctor;kw...) =
  DiagramHom(ob_maps, nothing, D, D′;kw...)

function DiagramHom(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor; cat=:id, kw...)
  is_op = cat == :op
  Ds = is_op ? (D, D′) : (D′, D)
  is_op || cat == :id || error("Bad diagram cat type $cat")
  f = if !is_op 
    FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′))
  else
    f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D′), dom(D))
  end 
  DiagramHom(f, mapvals(x -> cell2(first(Ds),x), ob_maps), Ds...; cat, kw...)
end

function DiagramHom(f::FinFunctor, components, D::FinDomFunctor, D′::FinDomFunctor;cat = :id, kw...)
  is_op = cat == :op 
  ϕ = if is_op 
    Transformation(components, f⋅D, D′)
  else 
    Transformation(components, D, f⋅D′)
  end
  DiagramHom{id}(f, ϕ, is_op ? D : D′;kw...)
end

# Helper functions
#-----------------

cell1(pair::Union{Pair,Tuple{Any,Any}}) = first(pair)
cell1(x) = x
cell2(::FinDomFunctor, pair::Union{Pair,Tuple{Any,Any}}) = last(pair)
cell2(D::FinDomFunctor, x) = id(codom(D), ob_map(D, x))

# # Categories of diagrams
# ########################

@instance ThCategory{FinDomFunctor, DiagramHom} [model::Diagram] begin 
  dom(f::DiagramHom) = dom(diagram_map(f))
  codom(f::DiagramHom) = dom(f.precomposed_diagram)
  id(X::FinDomFunctor) = DiagramHom(id(dom(X)), id(X), X)
  compose(f::DiagramHom, g::DiagramHom) = DiagramHom(
        shape_map(f) ⋅ shape_map(g),
        diagram_map(f) ⋅ (shape_map(f) * diagram_map(g)),
        codom_diagram(g))
end

@instance ThCategory{FinDomFunctor, DiagramHom} [model::DiagramOp] begin 
  dom(f::DiagramHom) = f.precomposed_diagram
  codom(f::DiagramHom) = codom(diagram_map(f))
  id(X::FinDomFunctor) = DiagramHom(id(dom(X)), id(X), X)
  compose(f::DiagramHom, g::DiagramHom) = DiagramHom(
    shape_map(g) ⋅ shape_map(f),
    (shape_map(g) * diagram_map(f)) ⋅ diagram_map(g),
    dom_diagram(f))
end

@instance ThCategory{FinDomFunctor, DiagramHom} [model::DiagramCo] begin 
  dom(f::DiagramHom) = codom(diagram_map(f))
  codom(f::DiagramHom) = f.precomposed_diagram
  id(X::FinDomFunctor) = DiagramHom(id(dom(X)), id(X), X)
  compose(f::DiagramHom, g::DiagramHom) = DiagramHom(
    shape_map(f) ⋅ shape_map(g),
    (shape_map(f) * diagram_map(g)) ⋅ diagram_map(f),
    codom_diagram(g))
end

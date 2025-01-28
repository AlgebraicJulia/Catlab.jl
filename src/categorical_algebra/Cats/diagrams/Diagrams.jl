export Diagram, DiagramHom, id, op, co,
  shape, diagram, shape_map, diagram_map, DiagramOp, DiagramCo

using StructEquality
using GATlab

import ....Theories: dom, codom, id, compose, ⋅, ∘, composeH
using ..Cats, ..FinCats, ..FreeDiagrams
using ..FinFunctors: mapvals, FinFunctor, FinDomFunctor
import ..FinFunctors: collect_ob, collect_hom, ob_map, hom_map, gen_map, force, op
using ..Transformations

# Morphisms of diagrams
#######################

@struct_hash_equal struct DiagramHom 
  shape_map::FinDomFunctor
  diagram_map::Transformation
  precomposed_diagram::FinDomFunctor
end

# Accessors
#----------
shape_map(f::DiagramHom) = f.shape_map

diagram_map(f::DiagramHom) = f.diagram_map

# Other methods
#--------------
force(f::DiagramHom) = 
  DiagramHom(force(shape_map(f)), diagram_map(f), force(f.precomposed_diagram))


op(f::DiagramHom) = DiagramHom(op.([shape_map(f), diagram_map(f), f.precomposed_diagram])...)

function Base.show(io::IO, f::DiagramHom)
  print(io, "DiagramHom(")
  print(io, shape_map(f))
  print(io, ", ")
  print(io, diagram_map(f))
  print(io, ", ")
  print(io, f.precomposed_diagram)
  print(io, ")")
end

""" The *shape* or *indexing category* of a diagram.

This is the domain of the functor.
"""
shape(d::FinDomFunctor) = dom(d)

ob_map(f::DiagramHom, x) = (ob_map(f.shape_map, x), component(f.diagram_map, x))

hom_map(f::DiagramHom, g) = hom_map(f.shape_map, g)

gen_map(f::DiagramHom, g) = gen_map(f.shape_map, g)

collect_ob(f::DiagramHom) =
  [(ob_map(f.shape_map, o), fₒ) for (o, fₒ) in pairs(components(f.diagram_map))]

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
abstract type AbsDiagramCat end 

@struct_hash_equal struct Diagram <: AbsDiagramCat end # {:id}

@struct_hash_equal struct DiagramOp <: AbsDiagramCat end

# TODO define this as op of DiagramOp?
@struct_hash_equal struct DiagramCo <: AbsDiagramCat end

# Constructors
##############

DiagramHom(ob_maps, D::FinDomFunctor, D′::FinDomFunctor;kw...) =
  DiagramHom(ob_maps, nothing, D, D′; kw...)

function DiagramHom(ob_maps, hom_map, D::FinDomFunctor, D′::FinDomFunctor; 
                    cat=:id, homtype=:hom, kw...)
  if cat == :id 
    f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′); homtype)
    DiagramHom(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′;kw...)
  elseif cat == :op 
    f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D′), dom(D); homtype)
    DiagramHom(f, mapvals(x -> cell2(D,x), ob_maps), D, D′; cat, kw...)
  elseif cat == :co 
    f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′); homtype)
    DiagramHom(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′;kw...)
  end 
end

function DiagramHom(f::FinFunctor, components, D::FinDomFunctor, 
                    D′::FinDomFunctor;cat = :id, kw...)
  ⋅ = compose[CatC()]
  if cat == :id 
    ϕ = Transformation(components, D, f⋅D′)
    DiagramHom(f, ϕ, D′)
  elseif cat == :op
    ϕ = Transformation(components, f⋅D, D′)
    DiagramHom(f, ϕ, D)
  elseif cat == :co 
    ϕ = Transformation(components, f⋅D′, D)
    DiagramHom(f, ϕ, D′)
  end
end

# Helper functions
#-----------------

cell1(pair::Union{Pair,Tuple{Any,Any}}) = first(pair)
cell1(x) = x
cell2(::FinDomFunctor, pair::Union{Pair,Tuple{Any,Any}}) = last(pair)
cell2(D::FinDomFunctor, x) = id(codom(D), ob_map(D, x))

# Categories of diagrams
########################

@instance ThCategory{FinDomFunctor, DiagramHom} [model::Diagram] begin 

  dom(f::DiagramHom) = dom(diagram_map(f))

  codom(f::DiagramHom) = f.precomposed_diagram

  id(X::FinDomFunctor) = DiagramHom(id(dom(X)), id(X), X)

  compose(f::DiagramHom, g::DiagramHom) = @withmodel Cat2() (⋅, *) begin 
      DiagramHom(shape_map(f) ⋅ shape_map(g), 
                 diagram_map(f) ⋅ ((shape_map(f) * diagram_map(g))), 
                 codom[model](g))
    end
  end

@instance ThCategory{FinDomFunctor, DiagramHom} [model::DiagramOp] begin 

  dom(f::DiagramHom) = f.precomposed_diagram

  codom(f::DiagramHom) = codom(diagram_map(f))

  id(X::FinDomFunctor) = 
    DiagramHom(id[FinCatC()](dom(X)), id[Cat2()](X), X)

  compose(f::DiagramHom, g::DiagramHom) = @withmodel Cat2() (⋅, *) begin
    DiagramHom(
      shape_map(g) ⋅ shape_map(f),
      (shape_map(g) * diagram_map(f)) ⋅ diagram_map(g),
      dom[model](f))
  end
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

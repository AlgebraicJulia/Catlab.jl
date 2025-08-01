export Diagram, DiagramId, DiagramOp, DiagramCo, DiagramHom, id, op, co,
  shape, diagram, shape_map, diagram_map, DiagramOp, DiagramCo, DiagramIdCat, 
  DiagramOpCat, DiagramCoCat

using StructEquality
using GATlab

import ....Theories: dom, codom, id, compose, ⋅, ∘, composeH
using ..Cats, ..FinCats, ..FreeDiagrams
using ..FinFunctors: mapvals, FinFunctor, FinDomFunctor
import ..FinFunctors: collect_ob, collect_hom, ob_map, hom_map, gen_map, force, op
import ..LimitsColimits: diagram
using ..Transformations

# Morphisms of diagrams
#######################
""" Diagram in a category.

Recall that a *diagram* in a category ``C`` is a functor ``D: J → C``, where for
us the *shape category* ``J`` is finitely presented. 
"""
abstract type Diagram end 

diagram(d::Diagram) = d.fun

""" The *shape* or *indexing category* of a diagram.

This is the domain of the functor.
"""
shape(d::Diagram) = dom(diagram(d))
force(d::T) where T<:Diagram = T(force(diagram(d)))
dom(d::Diagram) = dom(diagram(d))
codom(d::Diagram) = codom(diagram(d))
ob_map(d::Diagram, x) = ob_map(diagram(d), x)
hom_map(d::Diagram, f) = hom_map(diagram(d), f)
gen_map(d::Diagram, f) = gen_map(diagram(d), f)
collect_ob(d::Diagram) = collect_ob(diagram(d))
collect_hom(d::Diagram) = collect_hom(diagram(d))

"""
"""
@struct_hash_equal struct DiagramId <: Diagram 
  fun::FunctorFinDom 
end

DiagramId(d::Diagram) = DiagramId(diagram(d))

Diagram(f::FunctorFinDom) = DiagramId(f) # default

op(d::DiagramId) = DiagramOp(op(diagram(d)))

"""
"""
@struct_hash_equal struct DiagramOp <: Diagram 
  fun::FunctorFinDom 
end

DiagramOp(d::Diagram) = DiagramOp(diagram(d))

op(d::DiagramOp) = DiagramId(op(diagram(d)))

"""
"""
@struct_hash_equal struct DiagramCo <: Diagram 
  fun::FunctorFinDom 
end

DiagramCo(d::Diagram) = DiagramCo(diagram(d))

"""
There are several different
notions of morphism from a diagram ``D: J → C`` to another diagram 
``D′: J′ → C``

1. `DiagramId`: a functor ``F: J → J′`` together with a natural
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
@struct_hash_equal struct DiagramHom 
  shape_map::FinFunctor
  diagram_map::Transformation
  precomposed_diagram::Diagram
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


ob_map(f::DiagramHom, x) = (ob_map(f.shape_map, x), component(f.diagram_map, x))

hom_map(f::DiagramHom, g) = hom_map(f.shape_map, g)

gen_map(f::DiagramHom, g) = gen_map(f.shape_map, g)

collect_ob(f::DiagramHom) =
  [(ob_map(f.shape_map, o), fₒ) for (o, fₒ) in pairs(components(f.diagram_map))]

collect_hom(f::DiagramHom) = collect_hom(f.shape_map)

##########################
# Categories of diagrams #
##########################

abstract type DiagramCat end 
@struct_hash_equal struct DiagramIdCat <: DiagramCat end 
@struct_hash_equal struct DiagramOpCat <: DiagramCat end 
@struct_hash_equal struct DiagramCoCat <: DiagramCat end 

# Constructors
##############

DiagramHom(ob_maps, D::Diagram, D′::Diagram; kw...) =
  DiagramHom(ob_maps, nothing, D, D′; kw...)

function DiagramHom(ob_maps, hom_map, D::DiagramId, D′::DiagramId; homtype=:hom)
  f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′); homtype)
  DiagramHom(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′)
end

function DiagramHom(ob_maps, hom_map, D::DiagramOp, D′::DiagramOp; homtype=:hom)
  f = FinDomFunctor(mapvals(cell1, ob_maps), hom_map, dom(D′), dom(D); homtype)
  DiagramHom(f, mapvals(x -> cell2(D,x), ob_maps), D, D′)
end

function DiagramHom(ob_maps, hom_map, D::DiagramCo, D′::DiagramCo; homtype=:hom) 
  f = FinFunctor(mapvals(cell1, ob_maps), hom_map, dom(D), dom(D′); homtype)
  DiagramHom(f, mapvals(x -> cell2(D′,x), ob_maps), D, D′)
end

function DiagramHom(f::FinFunctor, components, D::DiagramId, D′::DiagramId; check=true)
  ϕ = Transformation(components, diagram(D), compose[CatC()](f,diagram(D′)); check)
  DiagramHom(f, ϕ, D′)
end

function DiagramHom(f::FinFunctor, components, D::DiagramOp, D′::DiagramOp; kw...)
  ϕ = Transformation(components, compose[CatC()](f,diagram(D)), diagram(D′))
  DiagramHom(f, ϕ, D)
end

function DiagramHom(f::FinFunctor, components, D::DiagramCo, D′::DiagramCo; kw...)
  ϕ = Transformation(components, compose[CatC()](f, diagram(D′)), diagram(D))
  DiagramHom(f, ϕ, D′)
end

# Helper functions
#-----------------

cell1(pair::Union{Pair,Tuple{Any,Any}}) = first(pair)
cell1(x) = x
cell2(::Diagram, pair::Union{Pair,Tuple{Any,Any}}) = last(pair)
cell2(D::Diagram, x) = id(codom(D), ob_map(D, x))

# Categories of diagrams
########################

@instance ThCategory{DiagramId, DiagramHom} [model::DiagramIdCat] begin 

  dom(f::DiagramHom) = DiagramId(dom(diagram_map(f)))

  codom(f::DiagramHom) = f.precomposed_diagram

  id(X::DiagramId) = DiagramHom(id(dom(X)), id(X), X)

  compose(f::DiagramHom, g::DiagramHom) = @withmodel Cat2() (⋅, *) begin 
      DiagramHom(shape_map(f) ⋅ shape_map(g), 
                 diagram_map(f) ⋅ ((shape_map(f) * diagram_map(g))), 
                 codom[model](g))
    end
  end

@instance ThCategory{DiagramOp, DiagramHom} [model::DiagramOpCat] begin 

  dom(f::DiagramHom) = f.precomposed_diagram

  codom(f::DiagramHom) = DiagramOp(codom(diagram_map(f)))

  id(X::DiagramOp) = 
    DiagramHom(id[FinCatC()](dom(X)), id[Cat2()](diagram(X)), X)

  compose(f::DiagramHom, g::DiagramHom) = @withmodel Cat2() (⋅, *) begin
    DiagramHom(
      shape_map(g) ⋅ shape_map(f),
      (shape_map(g) * diagram_map(f)) ⋅ diagram_map(g),
      dom[model](f))
  end
end

@instance ThCategory{DiagramCo, DiagramHom} [model::DiagramCoCat] begin 
  dom(f::DiagramHom) = DiagramCo(codom(diagram_map(f)))
  codom(f::DiagramHom) = f.precomposed_diagram
  id(X::DiagramCo) = DiagramHom(id(dom(X)), id(X), X)
  compose(f::DiagramHom, g::DiagramHom) = DiagramHom(
    shape_map(f) ⋅ shape_map(g),
    (shape_map(f) * diagram_map(g)) ⋅ diagram_map(f),
    codom_diagram(g))
end

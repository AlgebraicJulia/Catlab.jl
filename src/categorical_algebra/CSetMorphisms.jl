""" Morphisms of C-sets and attributed C-sets.
"""
module CSetMorphisms
export ACSetTransformation, CSetTransformation, components, dom, codom

using AutoHashEquals

using ..CSets, ..FinSets
using ...Theories: CatDesc, AttrDesc
import ...Theories: dom, codom

# Data types
############

""" Transformation between attributed C-sets.

A morphism of C-sets is a natural transformation: a transformation between
functors C -> Set satisfying the naturality axiom for all morphisms in C. This
struct records the data of a transformation; it does not enforce naturality.

The transformation has a component for every object in C. When C-sets have
attributes, the data types are assumed to be fixed. Thus, the naturality axiom
for data attributes is a commutative triangle, rather than a commutative square.
"""
@auto_hash_equals struct ACSetTransformation{CD <: CatDesc, AD <: AttrDesc{CD},
    Comp <: NamedTuple, Dom <: AbstractACSet{CD,AD}}
  components::Comp
  dom::Dom
  codom::Dom

  function ACSetTransformation{CD,AD}(components::NamedTuple{Ob},
                                      X::Dom, Y::Dom) where
      {Ob, CD <: CatDesc{Ob}, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}}
    components = NamedTuple{Ob}([
      coerce_component(ob, f, X, Y) for (ob, f) in pairs(components)
    ])
    new{CD,AD,typeof(components),Dom}(components, X, Y)
  end
end

function coerce_component(ob::Symbol, f::FinFunction{Int}, X, Y)
  @assert length(dom(f)) == nparts(X,ob) "Domain error in component $ob"
  @assert length(codom(f)) == nparts(Y,ob) "Codomain error in component $ob"
  return f
end
function coerce_component(ob::Symbol, f, X, Y)::FinFunction{Int}
  FinFunction(f, nparts(X,ob), nparts(Y,ob))
end

function ACSetTransformation(components::NamedTuple{Ob}, X::Dom, Y::Dom) where
    {Ob, CD <: CatDesc{Ob}, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}}
  ACSetTransformation{CD,AD}(components, X, Y)
end

function ACSetTransformation(X::Dom, Y::Dom; components...) where
    {Ob, CD <: CatDesc{Ob}, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}}
  @assert length(components) == length(Ob)
  components = NamedTuple{Ob}(Tuple(components[ob] for ob in Ob))
  ACSetTransformation{CD,AD}(components, X, Y)
end

const CSetTransformation{CD, Comp, Dom <: AbstractCSet{CD}} =
  ACSetTransformation{CD,AttrDesc{CD,(),(),(),()},Comp,Dom}

CSetTransformation(components, X::Dom, Y::Dom) where Dom <: AbstractCSet =
  ACSetTransformation(components, X, Y)
CSetTransformation(X::Dom, Y::Dom; components...) where Dom <: AbstractCSet =
  ACSetTransformation(X, Y; components...)

components(α::ACSetTransformation) = α.components
dom(α::ACSetTransformation) = α.dom
codom(α::ACSetTransformation) = α.codom

Base.getindex(α::ACSetTransformation, ob::Symbol) = α.components[ob]

end

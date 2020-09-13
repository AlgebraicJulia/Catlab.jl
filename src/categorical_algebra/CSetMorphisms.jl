""" Morphisms of C-sets and attributed C-sets.
"""
module CSetMorphisms
export ACSetTransformation, CSetTransformation, components, is_natural

using AutoHashEquals

using ...GAT, ..CSets, ..FinSets
import ..FinSets: force
using ...Theories: Category, CatDesc, AttrDesc
import ...Theories: dom, codom, compose, ⋅, id

# C-set transformations
#######################

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
    components = NamedTuple{Ob}(Tuple(
      coerce_component(ob, f, X, Y) for (ob, f) in pairs(components)
    ))
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
Base.getindex(α::ACSetTransformation, ob) = α.components[ob]

""" Is the transformation between C-sets a natural transformation?

Uses the fact that to check whether a transformation is natural, it suffices to
check the naturality equation on a generating set of morphisms.
"""
function is_natural(α::ACSetTransformation{CD,AD}) where {CD,AD}
  X, Y = dom(α), codom(α)
  for (f, c, d) in zip(CD.hom, CD.dom, CD.codom)
    Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
    all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf)) || return false
  end
  for (f, c) in zip(AD.attr, AD.adom)
    Xf, Yf, α_c = subpart(X,f), subpart(Y,f), α[c]
    all(Yf[α_c(i)] == Xf[i] for i in eachindex(Xf)) || return false
  end
  return true
end

force(α::ACSetTransformation) =
  ACSetTransformation(map(force, components(α)), dom(α), codom(α))

# Category of C-sets
####################

@instance Category{ACSet, ACSetTransformation} begin
  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  function id(X::ACSet)
    ACSetTransformation(map(t -> id(FinSet(length(t))), X.tables), X, X)
  end

  function compose(α::ACSetTransformation, β::ACSetTransformation)
    # Question: Should we incur cost of checking that codom(β) == dom(α)?
    ACSetTransformation(map(compose, components(α), components(β)),
                        dom(α), codom(β))
  end
end

end

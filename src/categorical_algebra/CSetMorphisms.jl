""" Morphisms of C-sets and attributed C-sets.
"""
module CSetMorphisms
export ACSetTransformation, CSetTransformation, components, is_natural

using Compat: isnothing

using AutoHashEquals
using StaticArrays: SVector

using ...GAT, ..CSets, ..FreeDiagrams, ..Limits, ..FinSets
import ..Limits: limit, colimit
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

  function ACSetTransformation{CD,AD}(components::NamedTuple, X::Dom, Y::Dom) where
      {Ob, CD <: CatDesc{Ob}, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}}
    @assert keys(components) ⊆ Ob
    coerced_components = NamedTuple{Ob}(
      coerce_component(ob, get(components, ob) do; Int[] end, X, Y)
      for ob in Ob)
    new{CD,AD,typeof(coerced_components),Dom}(coerced_components, X, Y)
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

ACSetTransformation(components::NamedTuple, X::Dom, Y::Dom) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}} =
  ACSetTransformation{CD,AD}(components, X, Y)
ACSetTransformation(X::Dom, Y::Dom; components...) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Dom <: AbstractACSet{CD,AD}} =
  ACSetTransformation{CD,AD}((; components...), X, Y)

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

  id(X::ACSet) = ACSetTransformation(map(id, finsets(X)), X, X)

  function compose(α::ACSetTransformation, β::ACSetTransformation)
    # Question: Should we incur cost of checking that codom(β) == dom(α)?
    ACSetTransformation(map(compose, components(α), components(β)),
                        dom(α), codom(β))
  end
end

finsets(X::ACSet) = map(table -> FinSet(length(table)), X.tables)

# Limits and colimits
#####################

# Compute limits and colimits of C-sets by reducing to those in FinSet using the
# "pointwise" formula for (co)limits in functor categories.

function limit(diagram::AbstractFreeDiagram{ACS}) where
    {CD <: CatDesc, ACS <: AbstractCSet{CD}}
  limits = map(limit, unpack_diagram(diagram))
  Xs = cone_objects(diagram)
  Y = ACS()
  for (c, lim) in pairs(limits)
    add_parts!(Y, c, length(ob(lim)))
  end
  for (f, c, d) in zip(CD.hom, CD.dom, CD.codom)
    Yfs = map(legs(limits[c]), Xs) do π, X
      compose(π, FinFunction(subpart(X, f), nparts(X, d)))
    end
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  πs = pack_components(map(legs, limits), map(X -> Y, Xs), Xs)
  Limit(diagram, Multispan(Y, πs))
end

function colimit(diagram::AbstractFreeDiagram{ACS}) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts, ACS <: AbstractACSet{CD,AD,Ts}}
  # Colimit of C-set without attributes.
  colimits = map(colimit, unpack_diagram(diagram))
  Xs = cocone_objects(diagram)
  Y = ACS()
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in zip(CD.hom, CD.dom, CD.codom)
    Yfs = map(legs(colimits[d]), Xs) do ι, X
      compose(FinFunction(subpart(X, f), nparts(X, d)), ι)
    end
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs))

  # Set data attributes by canonical inclusion from attributes in diagram.
  for (attr, c, d) in zip(AD.attr, AD.adom, AD.acodom)
    T = Ts.parameters[d]
    data = Vector{Union{Some{T},Nothing}}(nothing, nparts(Y, c))
    for (ι, X) in zip(ιs, Xs)
      for i in 1:nparts(X, c)
        j = ι[c](i)
        if isnothing(data[j])
          data[j] = Some(subpart(X, i, attr))
        else
          val1, val2 = subpart(X, i, attr), something(data[j])
          val1 == val2 || error(
            "ACSet colimit does not exist: $attr attributes $val1 != $val2")
        end
      end
    end
    set_subpart!(Y, attr, map(something, data))
  end

  Colimit(diagram, Multicospan(Y, ιs))
end

""" Diagram in C-Set → named tuple of diagrams in FinSet
"""
unpack_diagram(diagram::DiscreteDiagram{<:AbstractACSet}) =
  map(DiscreteDiagram, unpack_finsets(ob(diagram)))
unpack_diagram(span::Multispan{<:AbstractACSet}) =
  map(Multispan, finsets(apex(span)), unpack_components(legs(span)))
unpack_diagram(cospan::Multicospan{<:AbstractACSet}) =
  map(Multicospan, finsets(apex(cospan)), unpack_components(legs(cospan)))
unpack_diagram(para::ParallelMorphisms{<:AbstractACSet}) =
  map(ParallelMorphisms, unpack_components(hom(para)))

""" Vector of C-sets → named tuple of vectors of FinSets
"""
unpack_finsets(Xs::AbstractVector{<:AbstractACSet{CD}}) where
    {Ob, CD <: CatDesc{Ob}} =
  NamedTuple{Ob}([ map(X -> FinSet{Int,Int}(nparts(X, ob)), Xs) for ob in Ob ])

""" Vector of C-set transformations → named tuple of vectors of FinFunctions
"""
unpack_components(αs::AbstractVector{<:ACSetTransformation{CD}}) where
    {Ob, CD <: CatDesc{Ob}} =
  NamedTuple{Ob}([ map(α -> α[ob], αs) for ob in Ob ])

""" Named tuple of vectors of FinFunctions → vector of C-set transformations
"""
function pack_components(fs::NamedTuple{Ob}, doms, codoms) where Ob
  components = map((x...) -> NamedTuple{Ob}(x), fs...) # XXX: Is there a better way?
  map(ACSetTransformation, components, doms, codoms)
end

""" Objects in diagram that will have explicit legs in limit cone.

Encodes common conventions such as, when taking a pullback of a cospan, not
explicitly including a cone leg for the cospan apex since it can be computed
from the other legs.
"""
cone_objects(diagram) = ob(diagram)
cone_objects(cospan::Multicospan) = feet(cospan)
cone_objects(para::ParallelMorphisms) = SVector(dom(para))

""" Objects in diagram that will have explicit legs in colimit cocone.
"""
cocone_objects(diagram) = ob(diagram)
cocone_objects(span::Multispan) = feet(span)
cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

end

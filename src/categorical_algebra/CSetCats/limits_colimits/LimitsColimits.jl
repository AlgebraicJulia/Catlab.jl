module LimitsColimits 

using Reexport
using ACSets


using ...Cats
using ...Cats.FreeDiagrams: DiagramImpl, AbstractFreeDiagram
using ...Cats.LimitsColimits: LimitImpl, ColimitImpl, DefaultAlg
import ...Cats.LimitsColimits: _universal
using ..ACSetTransformations, ..CSets


# Dispatch 
##########

_universal(d::DiagramImpl, c::CatOfACSet, lim, sp) = 
  _universal(d, getvalue(c), lim, sp)

_universal(d::DiagramImpl, c::ACSetCategory, lim, sp) = 
  _universal(d, getvalue(c), lim, sp)

# Pointwise operations
######################

""" Diagram in C-Set → named tuple of diagrams in Set.
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet,<:Any}, C) =
  map(DiscreteDiagram, unpack_sets(ob(discrete), C))

unpack_diagram(span::Multispan{<:ACSet, <:Any}, C; kw...) =
  map(Multispan, sets(apex(span), C; kw...),
      unpack_components(legs(span), C; kw...))

unpack_diagram(cospan::Multicospan{<:ACSet}, C; kw...) =
  map(Multicospan, sets(apex(cospan), C; kw...),
      unpack_components(legs(cospan), C; kw...))

unpack_diagram(para::ParallelMorphisms{<:ACSet}, C; kw...) =
  map(ParallelMorphisms, unpack_components(hom(para), C; kw...))

unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
  map(ComposableMorphisms, unpack_components(hom(comp); kw...))

function unpack_diagram(diag::Union{AbsBipartiteFreeDiagram, 
                                    AbstractFreeDiagram}, C; kw...)
  S = acset_schema(C)
  NamedTuple(c => map(diag, Ob=X->get_ob[C](X,c), Hom=α->α[c]) for c in objects(S))
end

# function unpack_diagram(F::Functor)
#   res = NamedTuple(c => map(F, X->SetOb(X,c), α->α[c]) for c in objects(S))
#   if all || var 
#     return merge(res, NamedTuple(c => map(F, X->VarSet(X,c), α->α[c]) for c in attrtypes(S)))
#   end 
#   return res 
# end

""" Dispatch on Category type """
unpack_sets(Xs::AbstractVector{<:ACSet}, C::Category) = unpack_sets(Xs, getvalue(C))

""" Dispatch on ThCategory implementation """
unpack_sets(Xs::AbstractVector{<:ACSet}, C::TypeCat) = unpack_sets(Xs, getvalue(C))


""" Vector of C-sets → named tuple of vectors of sets.
"""
function unpack_sets(Xs::AbstractVector{<:ACSet}, C::CSetCat{S}) where S
  NamedTuple(c => map(X->get_ob[C](X, c), Xs) for c in objects(S))
end

function unpack_sets(Xs::AbstractVector{<:ACSet}, C::ACSetCat{S}) where S
  merge(NamedTuple(c => map(X->get_ob[C](X, c), Xs) for c in objects(S)),
        NamedTuple(c => map(X->get_attrtype[C](X, c), Xs) for c in attrtypes(S)))
end


""" Vector of C-set transformations → named tuple of vectors of functions.
"""
function unpack_components(αs::AbstractVector{<:ACSetTransformation}, 
                           ::CSetCat{S}) where S
  NamedTuple(c => map(α -> α[c], αs) for c in objects(S))
end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(fs::NamedTuple{names}, doms, codoms;
                         type_components=nothing) where names
  # XXX: Is there a better way?
  components = map((x...) -> NamedTuple{names}(x), fs...)
  if isnothing(type_components) || all(isempty,type_components)
    map(ACSetTransformation, components, doms, codoms)
  else 
    map(LooseACSetTransformation, components, type_components, doms, codoms)
  end
end

# Limits and Colimits
#####################
include("Limits.jl")
include("Colimits.jl")

@reexport using .Limits
@reexport using .Colimits

end # module

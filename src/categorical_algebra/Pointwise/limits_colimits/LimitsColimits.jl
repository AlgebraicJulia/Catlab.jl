
# By default, products of acsets are taken w.r.t. loose acset morphisms, whereas
# coproducts of acsets are taken w.r.t. tight acset morphisms. We do not need to
# provide defaults for limits and colimits of non-discrete diagrams, because the
# type of the diagram's morphisms disambiguates the situation.

kw_type(; loose::Bool=false, cset::Bool=false) = 
  if loose
    !cset || error("Cannot ask for a Loose CSetTransformation")
    LooseACSetTransformation
  elseif cset 
    CSetTransformation
  else 
    TightACSetTransformation
  end

""" Diagram in C-Set → named tuple of diagrams in Set.
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet}; kw...) =
  map(DiscreteDiagram, unpack_sets(ob(discrete); kw...))
unpack_diagram(span::Multispan{<:ACSet}; kw...) =
  map(Multispan, sets(apex(span); kw...),
      unpack_components(legs(span); kw...))
unpack_diagram(cospan::Multicospan{<:ACSet}; kw...) =
  map(Multicospan, sets(apex(cospan); kw...),
      unpack_components(legs(cospan); kw...))
unpack_diagram(para::ParallelMorphisms{<:ACSet}; kw...) =
  map(ParallelMorphisms, unpack_components(hom(para); kw...))
unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
  map(ComposableMorphisms, unpack_components(hom(comp); kw...))

function unpack_diagram(diag::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}};
                        S=nothing, Ts=nothing,all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(diag, Ob=X->SetOb(X,c), Hom=α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(diag, Ob=X->VarSet(X,c), Hom=α->α[c]) for c in attrtypes(S)))
  end
  return res 
end
function unpack_diagram(F::Functor{<:FinCat,<:TypeCat{ACS}};
                        S=nothing, Ts=nothing, all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(F, X->SetOb(X,c), α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(F, X->VarSet(X,c), α->α[c]) for c in attrtypes(S)))
  end 
  return res 
end

""" Vector of C-sets → named tuple of vectors of sets.
"""
function unpack_sets(Xs::AbstractVector{<:ACSet}; S=nothing, Ts=nothing,
                     all::Bool=false, var::Bool=false)
  # XXX: The explicit use of `FinSet` and `TypeSet` is needed here for the
  # nullary case (empty vector) because the Julia compiler cannot infer the
  # return type of the more general `SetOb`.
  fin_sets = NamedTuple(c => map(X->FinSet(X,c), Xs) for c in objects(S))
  if all
    return merge(fin_sets, (d => Vector{TypeSet}(map(X->TypeSet(X,d), Xs)) for d in attrtypes(S)))
  elseif var 
    return merge(fin_sets, map(attrtypes(S)) do d 
      T = VarSet{attrtype_instantiation(S,Ts,d)}
      d => T[T(nparts(X,d)) for X in Xs]
    end)
  else 
    return fin_sets
  end 
end

""" Vector of C-set transformations → named tuple of vectors of functions.
"""
function unpack_components(αs::AbstractVector{<:ACSetMorphism};
    S=nothing, Ts=nothing, all::Bool=false, var::Bool=false)
  res = NamedTuple(c => map(α -> α[c], αs) for c in objects(S))
  if !(all || var) return res end 
  f = var ? identity : type_components
  merge(res, NamedTuple(map(attrtypes(S)) do c 
  c => map(α-> f(α)[c] isa LooseVarFunction ? f(α)[c].loose : f(α)[c], αs)
  end))
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

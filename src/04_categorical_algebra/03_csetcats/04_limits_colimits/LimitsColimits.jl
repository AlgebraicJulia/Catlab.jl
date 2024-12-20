using ACSets, GATlab

export unpack

using ....BasicSets
using ...Cats
using ..ACSetTransformations, ..CSets
using ..ACSetCats#, ..PointwiseCats


""" 
Unpack a FreeDiagram{ACSet,ACSetTransformation} 
into a namedtuple of free diagrams, one for each ob/attrtype 
"""
function unpack(c::ACSetCategory, d::FreeDiagram)
  S = acset_schema(c)
  NamedTuple(merge(Dict(map(ob(S)) do o 
    o => fmap(d, x -> get_ob(c, x, o), x -> x[o])
  end..., map(attrtype(S)) do o 
    o => map(d, x -> get_attrtype(c, x, o), x -> x[o])
  end...)))
end

""" Map a function 𝒞 -> FreeDiagram -> X over a NamedTuple of Diagrams, where
the 𝒞 parameter is filled in for the entity category for each free diagram
keyed by an Ob and by the attr category for each diagram keyed by an AttrType.
"""
function map_prof(c::ACSetCategory, d::NamedTuple, f)
  mapvals(map_prof′(c, f), d)
end

function map_prof′(c, f)
  S = acset_schema(c)
  𝒞, 𝒟 = entity_cat(c), attr_cat(c)
  function closure(k, v)
    if k ∈ ob(S)
      f(𝒞, v)
    else 
      f(𝒟, v)
    end
  end
end

pointwise(lim) = 
  pack_limit(map_prof(model, unpack(model, d), lim))

@instance ThCategoryUnbiasedProducts{ACSet,ACSetTransformation,TerminalLimit,
                                      DiscreteDiagram, Multispan,ProductLimit
    }  [model::ACSetCategory{EC,AC,PC,O,H,AT,OP,A}
       ] where {EC,AC,PC,O,H,AT,OP,A} begin 
  @import compose, id, ◊

  ap(m::Multispan) = apex(m)

  ob(t::TerminalLimit) = t.ob

  function terminal()
    S = acset_schema(model)
    𝒞, 𝒟 = CatWithTerminal(entity_cat(model)), CatWithTerminal(attr_cat(model))
    unpacked = unpack(model, FreeDiagram(EmptyDiagram{ACSet}()))
    limits = NamedTuple(map(collect(pairs(unpacked))) do (k, v)
      k => ThCategoryWithTerminal.terminal(k ∈ ob(S) ? 𝒞 : 𝒟, getvalue(v))
    end)
    Xs = cone_objects(d)
    Y = pointwise_apex(model, Xs, limits)
    πs = pack_components(model, map(legs, limits), map(X -> Y, Xs), Xs)
    ProductLimit(Multispan(Y, πs))
  end

  universal(t::TerminalLimit, x::ACSet) = 
    pointwise_universal_limit(t, Multispan(x, ACSetTransformation[]))

  # compose(f::ACSetTransformation, g::ACSetTransformation) = compose(model, f,g)
  function product(d::DiscreteDiagram) 
    S = acset_schema(model)
    𝒞, 𝒟 = CatWithProducts(entity_cat(model)), CatWithProducts(attr_cat(model))
    unpacked = unpack(model, FreeDiagram(d))
    limits = NamedTuple(map(collect(pairs(unpacked))) do (k, v)
      k => ThCategoryUnbiasedProducts.product(k ∈ ob(S) ? 𝒞 : 𝒟, getvalue(v))
    end)
    Xs = cone_objects(d)
    Y = pointwise_apex(model, Xs, limits)
    πs = pack_components(model, map(legs, limits), map(X -> Y, Xs), Xs)
    ProductLimit(Multispan(Y, πs))
  end
  universal(t::ProductLimit, x::Multispan) = pointwise_universal_limit(t, x)

  ob(p::ProductLimit) = apex(p)
end 


function pointwise_apex(C::ACSetCategory, Xs, limits::NamedTuple)
  Y, S = constructor(C), acset_schema(C)
  𝒞 = CatWithProducts(entity_cat(C))
  for c in objects(S)
    add_parts!(Y, c, length(ob(𝒞, limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map((π, X) -> compose(𝒞, π,  get_hom(C, X, f)), legs(limits[c]), Xs)
    Yf = universal(𝒞, limits[d], Multispan(FinSet(ob(𝒞, limits[c])), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  return Y
end

# function pack_limit(c::ACSetCat, diagram::FreeDiagram, limits::NamedTuple)
#   Xs = cone_objects(diagram)
#   Y = constructor(c)
#   for c in objects(S)
#     add_parts!(Y, c, length(ob(limits[c])))
#   end
#   for (f, c, d) in homs(S)
#     Yfs = map((π, X) -> π ⋅ FinFunction(X, f), legs(limits[c]), Xs)
#     Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
#     set_subpart!(Y, f, collect(Yf))
#   end 
#   πs = pack_components(map(legs, merge(limits,alim)), map(X -> Y, Xs), Xs; 
#       type_components=type_components)
#   ACSetLimit(diagram, Multispan(Y, πs), limits)
# end


# Pointwise operations
######################

# """ Diagram in C-Set → named tuple of diagrams in Set.
# """
# unpack_diagram(discrete::DiscreteDiagram{<:ACSet,<:Any}, C) =
#   map(DiscreteDiagram, unpack_sets(ob(discrete), C))

# unpack_diagram(span::Multispan{<:ACSet, <:Any}, C; kw...) =
#   map(Multispan, sets(apex(span), C; kw...),
#       unpack_components(legs(span), C; kw...))

# unpack_diagram(cospan::Multicospan{<:ACSet}, C; kw...) =
#   map(Multicospan, sets(apex(cospan), C; kw...),
#       unpack_components(legs(cospan), C; kw...))

# unpack_diagram(para::ParallelMorphisms{<:ACSet}, C; kw...) =
#   map(ParallelMorphisms, unpack_components(hom(para), C; kw...))

# unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
#   map(ComposableMorphisms, unpack_components(hom(comp); kw...))

# function unpack_diagram(diag::Union{BipartiteFreeDiagram, 
#                                     AbstractFreeDiagram}, C; kw...)
#   S = acset_schema(C)
#   NamedTuple(c => map(diag, Ob=X->get_ob[C](X,c), Hom=α->α[c]) for c in objects(S))
# end

# function unpack_diagram(F::Functor)
#   res = NamedTuple(c => map(F, X->SetOb(X,c), α->α[c]) for c in objects(S))
#   if all || var 
#     return merge(res, NamedTuple(c => map(F, X->VarSet(X,c), α->α[c]) for c in attrtypes(S)))
#   end 
#   return res 
# end

# """ Dispatch on Category type """
# unpack_sets(Xs::AbstractVector{<:ACSet}, C::Category) = unpack_sets(Xs, getvalue(C))

# """ Dispatch on ThCategory implementation """
# unpack_sets(Xs::AbstractVector{<:ACSet}, C::TypeCat) = unpack_sets(Xs, getvalue(C))


# """ Vector of C-sets → named tuple of vectors of sets.
# """
# function unpack_sets(Xs::AbstractVector{<:ACSet}, C::CSetCat{S}) where S
#   NamedTuple(c => map(X->get_ob[C](X, c), Xs) for c in objects(S))
# end

# function unpack_sets(Xs::AbstractVector{<:ACSet}, C::ACSetCat{S}) where S
#   merge(NamedTuple(c => map(X->get_ob[C](X, c), Xs) for c in objects(S)),
#         NamedTuple(c => map(X->get_attrtype[C](X, c), Xs) for c in attrtypes(S)))
# end


# """ Vector of C-set transformations → named tuple of vectors of functions.
# """
# function unpack_components(αs::AbstractVector{<:ACSetTransformation}, 
#                            ::CSetCat{S}) where S
#   NamedTuple(c => map(α -> α[c], αs) for c in objects(S))
# end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(model::ACSetCategory, fs::NamedTuple{names}, doms, codoms) where names
  components = map((x...) -> NamedTuple{names}(x), fs...)
  models = map(_->model, fs)
  map(ACSetTransformation, components, doms, codoms, models)
end

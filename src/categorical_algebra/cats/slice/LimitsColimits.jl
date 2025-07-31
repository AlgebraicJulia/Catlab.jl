module SliceLimitsColimits 

using StructEquality
using GATlab

using ...Cats
import ...Cats: limit, colimit, universal
using ..SliceCategories

############
# Colimits #
############

@instance ThCategoryWithInitial{SliceOb{ObT, HomT}, SliceHom{ObT,HomT}} [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  colimit(::EmptyDiagram)::AbsColimit = 
    InitialColimit{SliceOb{<:ObT, <:HomT}, SliceHom{ObT,HomT}}(
      SliceOb(apex(initial[model.cat]()), create[model.cat](model.over)))

  universal(::AbsColimit, ::EmptyDiagram, a::Multicospan) = 
    FinFunction(Int[], FinSet(apex[model](a)))
end

@instance ThCategoryUnbiasedCoproducts{SliceOb{ObT, HomT}, SliceHom{ObT,HomT}} [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  colimit(d::DiscreteDiagram)::AbsColimit = colimit_slice(model, FreeDiagram(d))

  universal(colim::AbsColimit, diag::DiscreteDiagram, csp::Multicospan) = 
    slice_colimit_universal(model, colim, diag, csp)
end

@instance ThCategoryWithPushouts{SliceOb{ObT, HomT}, SliceHom{ObT,HomT}} [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  colimit(d::Multispan)::AbsColimit = colimit_slice(model, FreeDiagram(d))

  universal(colim::AbsColimit, diag::Multispan, csp::Multicospan) = 
    slice_colimit_universal(model, colim, diag, csp)
end

@instance ThCategoryWithBipartiteColimits{SliceOb{ObT, HomT}, SliceHom{ObT,HomT}} [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  colimit(d::BipartiteFreeDiagram)::AbsColimit = colimit_slice(model, FreeDiagram(d))

  universal(colim::AbsColimit, diag::BipartiteFreeDiagram, csp::Multicospan) = 
    slice_colimit_universal(model, colim, FreeDiagram(diag), csp)
end


""" 
Convert colimit in slice category into computation in the underlying category 
"""
function colimit_slice(model::SliceC, diagram::FreeDiagram)
  𝒞, D = model.cat, getvalue(diagram)
  Ob, Hom = impl_type(𝒞, ThCategory, :Ob), impl_type(𝒞, ThCategory, :Hom)
  # discard all the slice info in the colimit diagram - it's irrelevant
  colim = colimit[𝒞](fmap(D, x -> x.ob, x->x.hom, Ob, Hom))

  # compute new apex using the universal property of colimits
  csp = Multicospan(model.over, map(x -> x.hom, 
                    cocone_objects(D)); 
                    cat=𝒞)
  new_apex = SliceOb(ob(colim), universal[𝒞](colim, csp))
  new_legs = [SliceHom(A, new_apex, l; cat=𝒞) 
              for (A, l) in zip(cocone_objects(D), legs(colim))]
  cocone = Multicospan(new_apex, new_legs, cocone_objects(D))
  return ColimitCocone(cocone, diagram)
end

##########
# Limits #
##########
@instance ThCategoryUnbiasedProducts{SliceOb{ObT, HomT}, SliceHom{ObT,HomT}
    } [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  limit(d::DiscreteDiagram)::AbsLimit = limit_slice(model, FreeDiagram(d))

  universal(colim::AbsLimit, diag::DiscreteDiagram, csp::Multispan) = 
    slice_limit_universal(model, colim, FreeDiagram(diag), csp)
end

"""
A limit cone in a slice category 𝒞/X contains the limit cone data (where 
objects are SliceOb and morphisms are Homs in 𝒞) in addition to caching the 
limit in 𝒞 (which has a diagram with one extra object) in order to easily 
apply the universal property.
"""
@struct_hash_equal struct SliceLimitCone <: AbsLimit
  cone::Multispan
  diagram::FreeDiagram
  underlying::AbsLimit # in underlying 𝒞: `diagram` + 1 extra object
end

"""
Convert a limit problem in the slice category to a limit problem of the
underlying category.

Encode the base of slice as the first object in the new diagram
"""
function limit_slice(model, diagram::FreeDiagram)
  𝒞 = model.cat
  obs = [model.over, [x.ob for x in ob(diagram)]...] # one extra object

  # assumes that the Ob/Hom sets of `diagram` are Int! 
  # fix by making a Dict{Int,Ob} for input diagram
  homs = map(obset(diagram)) do o
    (obmap(diagram, o).hom,o+1,1)
  end ∪ map(homset(diagram)) do h 
    (hommap(diagram, h), src(diagram, h)+1, tgt(diagram, h)+1)
  end |> Vector{Tuple{impl_type(𝒞, ThCategory, :Hom), Int, Int}}

  FG = FreeGraph(obs,homs)
  lim = limit[𝒞](FG)

  new_apex = SliceOb(apex(lim), first(legs(lim.cone)))
  spn = Multispan(new_apex, legs(lim.cone)[2:end], FG[:ob][2:end])
  SliceLimitCone(spn, diagram, lim)
end

""" Use the universal property of the underlying category. """
function slice_limit_universal(model, lim::AbsLimit, _::FreeDiagram, sp::Multispan)
  𝒞, apx = model.cat, apex(sp)
  universal[𝒞](lim.underlying, Multispan(apx.ob, [apx.hom, sp...]; cat=𝒞))
end

end # module

module SliceLimits 

using ACSets: nparts
using ..SliceCategories

using ...FreeDiagrams, ...LimitsColimits
import ...LimitsColimits: limit, colimit, universal


struct SliceLimit{Hom, Ob <: Slice{Hom}, Diagram,
  Cone <: Multispan{Ob}} <: AbstractLimit{Ob,Diagram}
diagram::Diagram
cone::Cone
underlying::AbstractLimit
end

struct SliceColimit{Hom, Ob <: Slice{Hom}, Diagram,
    Cocone <: Multicospan{Ob}} <: AbstractColimit{Ob,Diagram}
diagram::Diagram
cocone::Cocone
underlying::AbstractColimit
end


"""
Get the underlying diagram of a slice category diagram which has the object
being sliced over explicitly, and arrows are ACSetTransformations

"""
function slice_diagram(f::FreeDiagram)::FreeDiagram
  obs = vcat([codom(f[:ob][1])], [dom(x.slice) for x in f[:ob]])
  homs = [(h.slice,i+1,1) for (i, h) in enumerate(f[:ob])]
  append!(homs, [(h.f, i+1, j+1) for (i,j,h) in zip(f[:src],f[:tgt],f[:hom])])
  FreeDiagram(obs,homs)
end

"""
Convert a limit problem in the slice category to a limit problem of the
underlying category.

Encode the base of slice as the first object in the new diagram
"""
function limit(::Type{Tuple{S,H}}, f::FreeDiagram) where {S<:Slice, H<:SliceHom}
  obs = [codom(f[:ob][1]), [dom(x.slice) for x in f[:ob]]...] # one extra object
  homs = [[(h.slice,i+1,1) for (i, h) in enumerate(f[:ob])]..., 
          [(h.f, i+1, j+1) for (i,j,h) in zip(f[:src],f[:tgt],f[:hom])]...]
  lim = limit(FreeDiagram(obs,homs))
  new_apex = Slice(first(legs(lim.cone)))
  new_cone_legs = [SliceHom(new_apex, ob, leg) for (ob, leg)
                   in zip(f[:ob],legs(lim.cone)[2:end])]
  return SliceLimit(f, Multispan(new_apex, new_cone_legs), lim)
end


colimit(s::Multispan{<:Slice}) = colimit(FreeDiagram{Slice,SliceHom}(s))

function colimit(::Type{Tuple{S,H}}, diagram::FreeDiagram) where {S<:Slice, H<:SliceHom}
  nparts(diagram, :V) > 0 ||
    error("Requires nonempty diagram in order to know what is sliced over")

  # discard all the slice info in the colimit diagram - it's irrelevant
  colim = colimit(map(diagram, ob = x -> dom(x.slice), hom = h -> h.f))

  # compute new apex using the universal property of colimits
  X = codom(first(diagram[:ob]))
  csp = Multicospan(X, map(x -> x.slice, diagram[:ob]))
  new_apex = Slice(universal(colim, csp))
  new_cocone_legs = [SliceHom(o, new_apex, l)
                     for (o, l) in zip(diagram[:ob],legs(colim))]
  return SliceColimit(diagram, Multicospan(new_apex, new_cocone_legs), colim)
end


function universal(lim::SliceLimit, sp::Multispan)
  # Use the universal property of the underlying category.
  apx = apex(sp)
  newspan = vcat([apx.slice],[x.f for x in sp])
  u = universal(lim.underlying, Multispan(dom(apx), newspan))
  apx2 = Slice(first(legs(lim.underlying.cone)))
  return SliceHom(apx, apx2, u)
end

end # module

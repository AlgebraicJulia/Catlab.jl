module Slices
export Slice, SliceHom

using AutoHashEquals
using ...GAT
using ..FreeDiagrams, ..Limits, ..CSets
using ...Theories: Category
import ...Theories: dom, codom, compose, id
import ..Limits: limit, colimit, universal
import ..FinSets: force, pushout_complement

"""
The data of the object of a slice category (say, some category C sliced over an
object X in Ob(C)) is the data of a homomorphism in Hom(A,X) for some ob A.
"""
@auto_hash_equals struct Slice{Hom}
  slice::Hom
end

"""
The data of the morphism of a slice category (call it h, and suppose a category
C is sliced over an object X in Ob(C)) between objects f and g is a homomorphism
in the underlying category that makes the following triangle commute.

   h
A --> B
f ↘ ↙ g
   X
"""
@auto_hash_equals struct SliceHom{Hom, Dom<:Slice, Codom<:Slice}
  dom::Dom
  codom::Codom
  f::Hom
end

function SliceHom(d::Dom, cd::Codom, f::Hom; strict::Bool=true) where {Dom,Codom,Hom}
  !strict || codom(d) == codom(cd) || error("$d and $cd not in same category")
  !strict || dom(d) == dom(f) || error("dom $d does not match $f")
  !strict || dom(cd) == codom(f) || error("codom $cd does not match $f")
  return SliceHom{Hom,Dom,Codom}(d, cd, f)
end

dom(s::Slice) = dom(s.slice)
codom(s::Slice) = codom(s.slice)
force(s::Slice)  = Slice(force(s.slice))
force(s::SliceHom) = SliceHom(
  force(dom(s)), force(codom(s)), force(s.f))


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


@instance Category{Slice, SliceHom} begin
  dom(f::SliceHom) = f.dom
  codom(f::SliceHom) = f.codom
  id(A::Slice) = SliceHom(A, A, id(dom(A.slice)))
  function compose(f::SliceHom, g::SliceHom; strict::Bool=false)
    !strict || codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SliceHom(dom(f), codom(g), compose(f.f, g.f))
  end
end

"""
Get the underlying diagram of a slice category diagram which has the object
being sliced over explicitly, and arrows are ACSetTransformations

Encode the base of slice as the first object in the diagram
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
"""
function limit(::Type{Tuple{S,H}}, diagram::FreeDiagram) where {S<:Slice, H<:SliceHom}
  lim = limit(slice_diagram(diagram))
  new_apex = Slice(first(legs(lim.cone)))
  new_cone_legs = [SliceHom(new_apex, ob, leg) for (ob, leg)
                   in zip(diagram[:ob],legs(lim.cone)[2:end])]
  return SliceLimit(diagram, Multispan(new_apex, new_cone_legs), lim)
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

"""    pushout_complement(f::SliceHom, g::SliceHom)
Compute a pushout complement in a slice category by using the pushout complement
in the underlying category.

     f
  B <-- A ---⌝
  | ↘ ↙      |
 g|  X       | f′
  ↓ ↗  ↖ cx  |
  D <--- C <--
      g′

"""
function pushout_complement(f::SliceHom, g::SliceHom)
    f′, g′ = pushout_complement(ComposablePair(f.f, g.f))
    D = codom(g)
    C = Slice(compose(g′, D.slice))
    return SliceHom(dom(f), C, f′) => SliceHom(C, D, g′)
end

end # module

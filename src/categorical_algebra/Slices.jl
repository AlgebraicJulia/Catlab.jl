module Slices
export Slice, SliceMorphism,SliceLimit

using ...GAT
using ..FreeDiagrams, ..Limits, ..CSets
using ...Theories: Category
import ...Theories: dom, codom, compose, id
import ..Limits: limit, universal
import ..FinSets: force

struct Slice{Ob,Hom}
    slice::Hom
end

struct SliceMorphism{Ob, Hom}
  dom::Slice{Ob, Hom}
  codom::Slice{Ob, Hom}
  f::Hom
  function SliceMorphism{Ob,Hom}(dom::Slice{Ob, Hom},codom::Slice{Ob, Hom},
                                 f::Hom) where {Ob, Hom}
    p1, p2 = force.([dom.slice, compose(f,codom.slice)])
    force(p1) == force(p2) ||
       error("Slice condition failed: \ndom.slice $p1\ncomposite $p2\nf " *
             "$(force(f))\ncodom $(force(codom.slice))")
    return new(dom, codom, f)
  end
end


dom(s::Slice)::StructACSet = dom(s.slice)
codom(s::Slice)::StructACSet = codom(s.slice)
force(s::Slice{Ob,Hom}) where {Ob,Hom} = Slice{Ob,Hom}(force(s.slice))
force(s::SliceMorphism{Ob,Hom}) where {Ob,Hom} = SliceMorphism{Ob,Hom}(
  force(dom(s)), force(codom(s)), force(s.f))


struct SliceLimit{Ob_, Hom, Ob <: Slice{Ob_,Hom}, Diagram,
                  Cone <: Multispan{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  underlying::AbstractLimit
end


@instance Category{Slice, SliceMorphism} begin
  dom(f::SliceMorphism) = f.dom
  codom(f::SliceMorphism) = f.codom
  id(A::Slice) = SliceMorphism(A, A, id(dom(A.slice)))
  function compose(f::SliceMorphism, g::SliceMorphism)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    typeof(f)(dom(f), codom(g), compose(f.f, g.f))
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
function limit(::Type{Tuple{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}},
               diagram::FreeDiagram{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}
               ) where {Ob, Hom}
  lim = limit(slice_diagram(diagram))
  new_apex = Slice{Ob,Hom}(first(legs(lim.cone)))
  new_cone_legs = [SliceMorphism{Ob,Hom}(new_apex, ob, leg) for (ob, leg)
                   in zip(diagram[:ob],legs(lim.cone)[2:end])]
  return SliceLimit(diagram, Multispan(new_apex, new_cone_legs), lim)
end

"""Use the universal property of the underlying category"""
function universal(lim::SliceLimit{Ob,Hom}, sp::Multispan) where {Ob, Hom}
  apx = apex(sp)
  newspan = vcat([apx.slice],[x.f for x in sp])
  u = universal(lim.underlying, Multispan(dom(apx), newspan))
  apx2 = Slice{Ob,Hom}(first(legs(lim.underlying.cone)))
  return SliceMorphism{Ob,Hom}(apx, apx2, u)
end

end # module
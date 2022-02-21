module Slices
export Slice, SliceMorphism,SliceLimit,SliceColimit, pushout_complement

using ...GAT
using ..FreeDiagrams, ..Limits, ..CSets
using ...Theories: Category
import ...Theories: dom, codom, compose, id
import ..Limits: limit, colimit, universal
import ..FinSets: force, pushout_complement

struct Slice{Ob,Hom}
  slice::Hom
end

struct SliceMorphism{Ob, Hom}
  dom::Slice{Ob, Hom}
  codom::Slice{Ob, Hom}
  f::Hom
  function SliceMorphism{Ob, Hom}(dom, codom, f) where {Ob, Hom}
    p1, p2 = force.([dom.slice, compose(f,codom.slice)])
    force(p1) == force(p2) ||
       error("Slice condition failed: \ndom.slice $p1\ncomposite $p2\nf " *
             "$(force(f))\ncodom $(force(codom.slice))")
    return new{Ob,Hom}(dom, codom, f)
  end
end

SliceMorphism(a,b,f) = SliceMorphism{typeof(a).parameters...}(a,b,f)


dom(s::Slice)::StructACSet = dom(s.slice)
codom(s::Slice)::StructACSet = codom(s.slice)
force(s::Slice{Ob,Hom}) where {Ob,Hom} = Slice{Ob,Hom}(force(s.slice))
force(s::SliceMorphism{Ob,Hom}) where {Ob,Hom} = SliceMorphism(
  force(dom(s)), force(codom(s)), force(s.f))


struct SliceLimit{Ob_, Hom, Ob <: Slice{Ob_,Hom}, Diagram,
                  Cone <: Multispan{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  underlying::AbstractLimit
end

struct SliceColimit{Ob_, Hom, Ob <: Slice{Ob_,Hom}, Diagram,
                    Cocone <: Multicospan{Ob}} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  underlying::AbstractColimit
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
limit(csp::Multicospan{<:Slice{Ob,Hom}}) where {Ob,Hom} = limit(FreeDiagram{Ob, Hom}(csp))

function limit(::Type{Tuple{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}},
               diagram::FreeDiagram{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}
               ) where {Ob, Hom}
  lim = limit(slice_diagram(diagram))
  new_apex = Slice{Ob,Hom}(first(legs(lim.cone)))
  new_cone_legs = [SliceMorphism(new_apex, ob, leg) for (ob, leg)
                   in zip(diagram[:ob],legs(lim.cone)[2:end])]
  return SliceLimit(diagram, Multispan(new_apex, new_cone_legs), lim)
end

"""Warning: requires nonempty diagram in order to know what is sliced over"""
colimit(sp::Multispan{<:Slice{Ob,Hom}}) where {Ob,Hom} = colimit(FreeDiagram{Slice{Ob,Hom}, SliceMorphism{Ob,Hom}}(sp))
colimit(::Type{Tuple{SliceMorphism{Ob, Hom}, Any}},
                 p::ObjectPair{<:SliceMorphism}) where {Ob, Hom} =
  colimit(Span(p[1], p[2]))

function colimit(::Type{Tuple{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}},
                  diagram::FreeDiagram{Slice{Ob, Hom}, SliceMorphism{Ob, Hom}}) where {Ob, Hom}
  # discard all the slice info in the colimit diagram - it's irrelevant
  obs  = [x.slice for x in diagram[:ob]]
  obdoms = dom.(obs)
  X = codom(first(diagram[:ob]))
  homs = [(h.f, s, t) for (h, s, t) in zip(diagram[:hom], diagram[:src], diagram[:tgt])]
  colim = colimit(FreeDiagram(obdoms,homs))
  csp = Multicospan(X, obs)
  new_apex = Slice{Ob, Hom}(universal(colim, csp))
  new_cocone_legs = [SliceMorphism(o, new_apex, l)
                     for (o, l) in zip(diagram[:ob],legs(colim))]
  # compute new apex using the universal property of colimits
  return SliceColimit(diagram, Multicospan(new_apex, new_cocone_legs), colim)
end

"""Use the universal property of the underlying category"""
function universal(lim::SliceLimit{Ob,Hom}, sp::Multispan) where{Ob, Hom}
  apx = apex(sp)
  newspan = vcat([apx.slice],[x.f for x in sp])
  u = universal(lim.underlying, Multispan(dom(apx), newspan))
  apx2 = Slice{Ob,Hom}(first(legs(lim.underlying.cone)))
  return SliceMorphism(apx, apx2, u)
end


function pushout_complement(f::SliceMorphism{Ob, Hom}, g::SliceMorphism{Ob, Hom}
    )::Pair{SliceMorphism{Ob, Hom}, SliceMorphism{Ob, Hom}} where {S, Ob <: StructACSet{S}, Hom <: ACSetTransformation}
    f_, g_ = pushout_complement(ComposablePair(f.f, g.f))
    D__ = Slice{Ob, Hom}(compose(g_, codom(g).slice))
    g__ = SliceMorphism(D__, codom(g), g_)
    f__ = SliceMorphism(dom(f), D__, f_)
    return f__ => g__
end

end # module
using DataStructures
using StaticArrays: StaticVector, SVector
using ACSets 
using ....BasicSets, ....Graphs, ...Cats
import ...Cats: colimit, universal

colimit(Xs::EmptyDiagram{<:FinSet{Int}}) = Colimit(Xs, SMulticospan{0}(FinSet(0)))

function universal(colim::Initial{<:FinSet{Int}}, cocone::SMulticospan{0})
  cod = apex(cocone)
  FinDomFunction(SVector{0,eltype(cod)}(), cod)
end

colimit(Xs::SingletonDiagram{<:FinSet{Int}}) = colimit(Xs, SpecializeColimit())

function colimit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Colimit(Xs, Cospan(ι1, ι2))
end

function universal(colim::BinaryCoproduct{<:FinSet{Int}}, cocone::Cospan)
  f, g = cocone
  FinDomFunction(vcat(collect(f), collect(g)), ob(colim), apex(cocone))
end

function colimit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0,cumsum(ns)...]
  ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
  Colimit(Xs, Multicospan(FinSet(n), ιs))
end

function universal(colim::Coproduct{<:FinSet{Int}}, cocone::Multicospan)
  cod = apex(cocone)
  FinDomFunction(mapreduce(collect, vcat, cocone, init=eltype(cod)[]),
                 ob(colim), cod)
end

function colimit(pair::ParallelPair{<:FinSet{Int},T,K}) where {T,K} 
  f, g = pair
  m, n = length(dom(pair)), length(codom(pair))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  Colimit(pair, SMulticospan{1}(quotient_projection(sets)))
end

function colimit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  Colimit(para, SMulticospan{1}(quotient_projection(sets)))
end

function universal(coeq::Coequalizer{<:FinSet{Int}}, cocone::Multicospan)
  pass_to_quotient(proj(coeq), only(cocone))
end

""" Create projection map π: X → X/∼ from partition of X.
"""
function quotient_projection(sets::IntDisjointSets)
  h = [ find_root!(sets, i) for i in 1:length(sets) ]
  roots = unique!(sort(h))
  FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction{Int,Int}, h::FinFunction{Int,Int})
  @assert dom(π) == dom(h)
  q = zeros(Int, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(==(0), q) && error("Projection map is not surjective")
  FinFunction(q, codom(h))
end

function pass_to_quotient(π::FinFunction{Int,Int}, h::FinDomFunction{Int})
  @assert dom(π) == dom(h)
  q = Vector{Union{Some{eltype(codom(h))},Nothing}}(nothing, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if isnothing(q[j])
      q[j] = Some(h(i))
    else
      something(q[j]) == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(isnothing, q) && error("Projection map is not surjective")
  FinDomFunction(map(something, q), codom(h))
end

function colimit(span::Multispan{<:FinSet{Int}})
  colimit(span, ComposeCoproductCoequalizer())
end

""" Colimit of general diagram of FinSets computed by coproduct-then-quotient.

See `Limits.CompositePushout` for a very similar construction.
"""
struct FinSetCompositeColimit{Ob<:FinSet, Diagram,
                              Cocone<:Multicospan{Ob}, Coprod<:Coproduct{Ob},
                              Proj<:FinFunction} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  proj::Proj # Projection for the "multi-coequalizer" in general formula.
end

function colimit(d::BipartiteFreeDiagram{<:FinSet{Int}})
  # As in a pushout, this method assume that all objects in layer 1 have
  # outgoing morphisms so that they can be excluded from the coproduct.
  @assert !any(isempty(incident(d, u, :src)) for u in vertices₁(d))
  coprod = coproduct(FinSet{Int}[ob₂(d)...])
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for u in vertices₁(d)
    out_edges = incident(d, u, :src)
    for (e1, e2) in zip(out_edges[1:end-1], out_edges[2:end])
      h1, h2 = hom(d, e1), hom(d, e2)
      ι1, ι2 = ιs[tgt(d, e1)], ιs[tgt(d, e2)]
      for i in ob₁(d, u)
        union!(sets, ι1(h1(i)), ι2(h2(i)))
      end
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan(codom(π), [ ιs[i]⋅π for i in vertices₂(d) ])
  FinSetCompositeColimit(d, cocone, coprod, π)
end

colimit(d::FreeDiagram{<:FinSet{Int}}) = colimit(FinDomFunctor(d))

function colimit(F::Functor{<:FinCat{Int},<:TypeCat{<:FinSet{Int}}})
  # Uses the general formula for colimits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.2.16).
  J = dom(F)
  coprod = coproduct(map(x -> ob_map(F, x)::FinSet{Int,Int}, ob_generators(J)))
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for f in hom_generators(J)
    s, t, h = dom(J, f), codom(J, f), hom_map(F, f)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan(codom(π), map(x -> ιs[x]⋅π, ob_generators(J)))
  FinSetCompositeColimit(F, cocone, coprod, π)
end

function universal(colim::FinSetCompositeColimit, cocone::Multicospan)
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end

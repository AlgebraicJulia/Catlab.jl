module FinSetCatColimits 

using StructEquality, StaticArrays

using GATlab

using .....Theories, .....Graphs, .....BasicSets
using ....Cats
using ..FinSetCat: FinSetC

# Initial object
################

@instance ThCategoryWithInitial{FinSet,FinFunction,AbsSet,AbsColimit,    Multicospan, EmptyDiagram} [model::FinSetC] begin 

  colimit(::EmptyDiagram) =
    InitialColimit{FinSet,FinFunction}(FinSet(EmptySet()))
    
  universal(::AbsColimit, ::EmptyDiagram, x::Multicospan) =
    FinFunction(eltype(apex(x))[], apex(x))
end 

# Coproducts
############

@instance ThCategoryUnbiasedCoproducts{FinSet,FinFunction,AbsSet,AbsColimit,
    Multicospan, DiscreteDiagram} [model::FinSetC] begin

  function colimit(d::DiscreteDiagram)::AbsColimit
    Xs = collect(d)
    S = SumSet(Xs) |> FinSet
    ιs = [FinFunction(SetFunctionCallable(i->TaggedElem(i, j), X, S)) 
          for (j, X) in enumerate(Xs)]
    csp = Multicospan{FinSet, FinFunction}(S, ιs, Xs)
    ColimitCocone(csp, FreeDiagram(d))
  end

  function universal(lim::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    fun(t::TaggedElem) = cocone[getidx(t)](getvalue(t))
    FinFunction(SetFunctionCallable(fun, ob(lim), FinSet(apex(cocone))))  
  end
end

if false 

""" Coproduct in FinSet """
function colimit(Xs::DiscreteDiagram, m::SetC, ::DefaultAlg′)
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0, cumsum(ns)...]
  ιs = map(1:length(ns)) do j 
    FinFunction((1:ns[j]) .+ offsets[j], n) 
  end
  Colimit(Diagram(Xs, Category(TypeCat(m))), Multicospan(FinSet(n), ιs))
end

function _universal(::DiscreteDiagram, ::SetC, ::ColimitCocone, cocone::Multicospan{Ob,Hom}) where {Ob,Hom}
  cod = apex(cocone)
  FinDomFunction(mapreduce(collect, vcat, cocone, init=Int[]), cod)
end



# Coequalizers
##############

""" Equalizer in FinSet """
function colimit(para::ParallelMorphisms{Ob,Hom}, c::SetC, ::DefaultAlg′) where {Ob,Hom}
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  q = quotient_projection(sets)
  Colimit(Diagram(para, Category(TypeCat(c))), Multicospan([q]))
end

function _universal(::ParallelMorphisms, ::SetC, res::ColimitCocone, x::Multicospan)
  pass_to_quotient(only(cocone(res)), only(x))
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
function pass_to_quotient(π::FinFunction, h::FinFunction)
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

function pass_to_quotient(π::FinFunction, h::FinDomFunction)
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



"""
Colimit in FinSet.

As in a pushout, this method assume that all objects in layer 1 have
outgoing morphisms so that they can be excluded from the coproduct.
"""
function colimit(d::AbsBipartiteFreeDiagram, m::SetC, ::DefaultAlg′)
  @assert !any(isempty(incident(d, u, :src)) for u in vertices₁(d))
  coprod = coproduct(ob₂(d), Category(TypeCat(m)))
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
  cocone = Multicospan(codom(π), [compose[m](ιs[i],π) for i in vertices₂(d) ])
  Colimit(Diagram(d, Category(TypeCat(m))), CompositeColimit(cocone, coprod, π))
end

""" 
Colimit in FinSet. Uses the general formula for colimits in Set 
(Leinster, 2014, Basic Category Theory, Example 5.2.16).
"""
function colimit(F::FreeDiagram{Ob,Hom}, m::SetC, ::DefaultAlg′) where {Ob,Hom}
  coprod = coproduct(ob(F), Category(TypeCat(m)))
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for e in edges(F)
    s, t, h = src(F, e), tgt(F, e), hom(F, e)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan{Ob,Hom}(map(ι -> compose[m](ι,π), ιs))
  Colimit(Diagram(F, Category(TypeCat(m))),CompositeColimit(cocone, coprod, π))
end

function _universal(::Union{FreeDiagram,AbsBipartiteFreeDiagram}, ::SetC, colim::CompositeColimit, cocone::Multicospan)
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end


""" Default algorithm for a colimit of a span is ComposeCoproductCoequalizer """
colimit(span::Multispan, m::SetC, ::DefaultAlg′) =   
  colimit(span, Category(TypeCat(m)), ComposeCoproductCoequalizer())

# Colimits with names
#--------------------

"""
If the diagram is in skeleton of FinSet, use `DefaultAlg′`. Otherwise, used 
`NamedColimit` algorithm which is only defined for BipartiteFreeDiagrams
Reducing to the case of bipartite free diagrams is a bit lazy, but at least
using `specialize` below should avoid some gross inefficiencies.
"""
function colimit(d::DiagramImpl, m::SetC, ::DefaultAlg)
  is_diag_finsetint(d) && return colimit(d, m, DefaultAlg′())
  colimit(BipartiteFreeDiagram(d), m, NamedColimit())
end 

""" Every object in the diagram is a FinSet """
is_diag_finsetint(d::DiagramImpl) = all(x-> getvalue(x) isa FinSet, objects(d))

""" 
Compute colimit of diagram in the skeleton of FinSet (`FinSet{Int}`).
Note: no performance would be gained by using `DisjointSets{T}` from
DataStructures.jl because it is just a wrapper around `IntDisjointSets` that
internally builds the very same indices that we use below.
"""
function colimit(d::BipartiteFreeDiagram{Ob,Hom}, m::SetC, ::NamedColimit) where {Ob,Hom}
  sets₁_skel = map(set -> skeletize(set, index=false), ob₁(d))
  sets₂_skel = map(set -> skeletize(set, index=true), ob₂(d))
  funcs = map(edges(d)) do e
    skeletize(hom(d,e), sets₁_skel[src(d,e)], sets₂_skel[tgt(d,e)])
  end
  d_skel = BipartiteFreeDiagram{FinSet,FinDomFunction}()
  add_vertices₁!(d_skel, nv₁(d), ob₁=dom.(sets₁_skel))
  add_vertices₂!(d_skel, nv₂(d), ob₂=dom.(sets₂_skel))
  add_edges!(d_skel, src(d), tgt(d), hom=funcs)

  # PROBLEM: if we `specialize` here, it changes the # of legs of the colimit!
  # But computing `ιs` requires bijection between `colim_skel` and `sets₂_skel`
  # We want to `specialize` to make the colimit more efficient, though.
  colim_skel = colimit(d_skel, m, DefaultAlg′())

  # Assign elements/names to the colimit set.
  elems = Vector{Symbol}(undef, length(apex(colim_skel)))
  for (ι, Y) in zip(colim_skel, sets₂_skel)
    for i in dom(Y)
      elems[ι(i)] = Y(i)
    end
  end
  # The vector should already be filled, but to reduce arbitrariness we prefer
  # names from the layer 1 sets whenever possible. For example, when computing a
  # pushout, we prefer names from the apex of cospan to names from the feet.
  for (u, X) in zip(vertices₁(d_skel), sets₁_skel)
    e = first(incident(d_skel, u, :src))
    f, ι = hom(d_skel, e), legs(colim_skel)[tgt(d_skel, e)]
    for i in dom(X)
      elems[ι(f(i))] = X(i)
    end
  end
  # Eliminate clashes in provisional list of names.
  unique_by_tagging!(elems)
  ιs = map(colim_skel, sets₂_skel) do ι, Y
    FinFunction(Dict(Y(i) => elems[ι(i)] for i in dom(Y)), FinSet(Set(elems)))
  end
  Colimit(Diagram(d, Category(TypeCat(m))), Multicospan(FinSet(Set(elems)), ιs))
end

function skeletize(set::FinSet; index::Bool=false)
  # FIXME: We should support `unique_index` and it should be used here.
  FinDomFunction(collect(set), set, index=index)
end
function skeletize(f::FinFunction, X, Y)
  FinFunction(i -> only(preimage(Y, f(X(i)))), dom(X), dom(Y))
end

""" Make list of elements unique by adding tags if necessary.

If the elements are already unique, they will not be mutated.
"""
function unique_by_tagging!(elems::AbstractVector{T}; tag=default_tag) where T
  tag_count = Dict{T,Int}()
  for x in elems
    tag_count[x] = haskey(tag_count, x) ? 1 : 0
  end
  for (i, x) in enumerate(elems)
    (j = tag_count[x]) > 0 || continue
    tagged = tag(x, j)
    @assert !haskey(tag_count, tagged) # Don't conflict with original elems!
    elems[i] = tagged
    tag_count[x] += 1
  end
  elems
end

default_tag(x::Symbol, t) = Symbol(x, "#", t)
default_tag(x::AbstractString, t) = string(x, "#", t)

end 

end # module

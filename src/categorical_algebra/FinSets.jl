""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinFunction, FinFunctionCallable, FinFunctionVector, force

using Compat: only

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root!
using FunctionWrappers: FunctionWrapper

using ...Theories, ..FreeDiagrams, ..Limits, ..Sets
import ...Theories: dom, codom
import ..Limits: limit, colimit, universal
using ..Sets: SetFunctionIdentity

# Data types
############

""" Finite set.

This generic type encompasses the category **FinSet** of finite sets and
functions, through types `FinSet{S} where S <: AbstractSet`, as well as the
skeleton of this category, through the type `FinSet{Int}`. In the latter case,
the object `FinSet(n)` represents the set ``{1,...,n}``.
"""
@auto_hash_equals struct FinSet{S,T} <: SetOb{T}
  set::S
end

FinSet(n::Int) = FinSet{Int,Int}(n)
FinSet(set::S) where {T,S<:AbstractSet{T}} = FinSet{S,T}(set)
FinSet(s::FinSet) = s

Base.iterate(s::FinSet, args...) = iterate(iterable(s), args...)
Base.length(s::FinSet) = length(iterable(s))
Base.in(s::FinSet, elem) = in(s, iterable(s))
iterable(s::FinSet{Int}) = 1:s.set
iterable(s::FinSet{<:AbstractSet}) = s.set

Base.show(io::IO, s::FinSet) = print(io, "FinSet($(s.set))")

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the latter
case, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented by the
vector [1,3,2,3].
"""
const FinFunction{S, S′, Dom <: FinSet{S}, Codom <: FinSet{S′}} =
  SetFunction{Dom,Codom}

FinFunction(f::Function, args...) = FinFunctionCallable(f, args...)
FinFunction(f::AbstractVector, args...) = FinFunctionVector(f, args...)
FinFunction(::typeof(identity), args...) = FinFunctionIdentity(args...)

""" Function in **FinSet** defined by a callable Julia object.

Is evaluated lazily unless forced via [`force`](@ref).
"""
const FinFunctionCallable{S,S′,T,T′} =
  SetFunctionCallable{T,T′,FinSet{S,T},FinSet{S′,T′}}

FinFunctionCallable(f, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), FinSet(codom))

function Base.show(io::IO, f::FinFunctionCallable)
  func = f.func.obj[] # Deference FunctionWrapper
  print(io, "FinFunction($(nameof(func)), $(f.dom), $(f.codom))")
end

""" Function in **FinSet** represented explicitly by a vector.

The elements of the set are assumed to be ``{1,...,n}``.
"""
@auto_hash_equals struct FinFunctionVector{S′,T′,V<:AbstractVector{T′}} <:
    SetFunction{FinSet{Int,Int},FinSet{S′,T′}}
  func::V
  codom::FinSet{S′,T′}
end

FinFunctionVector(f::AbstractVector{Int}) =
  FinFunctionVector(f, isempty(f) ? 0 : maximum(f))
FinFunctionVector(f::AbstractVector, codom) = FinFunctionVector(f, FinSet(codom))
FinFunctionVector(f::AbstractVector, dom::Int, codom) =
  FinFunctionVector(f, FinSet(dom), FinSet(codom))

function FinFunctionVector(f::AbstractVector, dom::FinSet{Int}, codom::FinSet)
  length(f) == length(dom) ||
    error("Length of vector $f does not match domain $dom")
  FinFunctionVector(f, codom)
end

dom(f::FinFunctionVector) = FinSet(length(f.func))

Sets.compose_impl(f::FinFunctionVector, g::FinFunctionVector) =
  FinFunctionVector(g.func[f.func], g.codom)

Base.show(io::IO, f::FinFunctionVector) =
  print(io, "FinFunction($(f.func), $(length(f.func)), $(length(f.codom)))")

(f::FinFunctionVector)(x) = f.func[x]

""" Force evaluation of lazy function or relation.
"""
force(f::FinFunction{Int}) = FinFunctionVector(map(f, dom(f)), codom(f))
force(f::FinFunctionVector) = f

Base.collect(f::FinFunction) = force(f).func

""" Identity function in **Set**.
"""
const FinFunctionIdentity{S,T} = SetFunctionIdentity{FinSet{S,T}}

FinFunctionIdentity(dom) = SetFunctionIdentity(FinSet(dom))
FinFunctionIdentity(dom, codom) = SetFunctionIdentity(FinSet(dom), FinSet(codom))

Base.show(io::IO, f::FinFunctionIdentity) =
  print(io, "FinFunction(identity, $(f.dom))")

# Limits
########

function limit(Xs::EmptyDiagram{<:FinSet{Int}})
  Limit(Xs, SMultispan{0}(FinSet(1)))
end

function universal(lim::Terminal{<:FinSet{Int}},
                   cone::SMultispan{0,<:FinSet{Int}})
  FinFunction(ones(Int, length(apex(cone))))
end

function limit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::BinaryProduct{<:FinSet{Int}}, cone::Span{<:FinSet{Int}})
  f, g = cone
  m, n = length.(codom.(cone))
  indices = LinearIndices((m, n))
  FinFunction(i -> indices[f(i),g(i)], apex(cone), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = [FinFunction(i -> indices[i][j], n, ns[j]) for j in 1:length(ns)]
  Limit(Xs, Multispan(FinSet(n), πs))
end

function universal(lim::Product{<:FinSet{Int}}, cone::Multispan{<:FinSet})
  ns = length.(codom.(cone))
  indices = LinearIndices(Tuple(ns))
  FinFunction(i -> indices[(f(i) for f in cone)...], apex(cone), ob(lim))
end

function limit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m = length(dom(pair))
  eq = FinFunction(filter(i -> f(i) == g(i), 1:m), m)
  Limit(pair, SMultispan{1}(eq))
end

function limit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(para, SMultispan{1}(eq))
end

function universal(lim::Equalizer{<:FinSet{Int}},
                   cone::SMultispan{1,<:FinSet{Int}})
  ι = collect(incl(lim))
  h = only(cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end

limit(cospan::Multicospan{<:FinSet{Int}}) = composite_pullback(cospan)

""" Limit of free diagram of FinSets.

See `CompositePullback` for a very similar construction.
"""
struct FinSetFreeDiagramLimit{Ob<:FinSet, Diagram<:FreeDiagram{Ob},
                              Cone<:Multispan{Ob}, Prod<:Product{Ob},
                              Incl<:FinFunction} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  incl::Incl # Inclusion for the "multi-equalizer" in general formula.
end

function limit(d::FreeDiagram{<:FinSet{Int}})
  # Uses the general formula for limits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.1.22 / Equation 5.16).
  prod = product(ob(d))
  n, πs = length(ob(prod)), legs(prod)
  ι = FinFunction(filter(1:n) do i
    all(begin
          s, t, h = src(d,e), tgt(d,e), hom(d,e)
          h(πs[s](i)) == πs[t](i)
        end for e in edges(d))
    end, n)
  cone = Multispan(dom(ι), [compose(ι,πs[i]) for i in vertices(d)])
  FinSetFreeDiagramLimit(d, cone, prod, ι)
end

function universal(lim::FinSetFreeDiagramLimit, cone::Multispan{<:FinSet{Int}})
  ι = collect(lim.incl)
  h = universal(lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)],
              apex(cone), ob(lim))
end

# Colimits
##########

function colimit(Xs::EmptyDiagram{<:FinSet{Int}})
  Colimit(Xs, SMulticospan{0}(FinSet(0)))
end

function universal(colim::Initial{<:FinSet{Int}},
                   cocone::SMulticospan{0,<:FinSet{Int}})
  FinFunction(Int[], apex(cocone))
end

function colimit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Colimit(Xs, Cospan(ι1, ι2))
end

function universal(colim::BinaryCoproduct{<:FinSet{Int}},
                   cocone::Cospan{<:FinSet{Int}})
  f, g = cocone
  FinFunction(vcat(collect(f), collect(g)), ob(colim), apex(cocone))
end

function colimit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0,cumsum(ns)...]
  ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
  Colimit(Xs, Multicospan(FinSet(n), ιs))
end

function universal(colim::Coproduct{<:FinSet{Int}},
                   cocone::Multicospan{<:FinSet{Int}})
  FinFunction(reduce(vcat, (collect(f) for f in cocone), init=Int[]),
              ob(colim), apex(cocone))
end

function colimit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m, n = length(dom(pair)), length(codom(pair))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h], length(roots))
  Colimit(pair, SMulticospan{1}(coeq))
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
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
  Colimit(para, SMulticospan{1}(coeq))
end

function universal(coeq::Coequalizer{<:FinSet{Int}},
                   cocone::SMulticospan{1,<:FinSet{Int}})
  pass_to_quotient(proj(coeq), only(cocone))
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
      @assert q[j] == h(i) "Quotient map out of coequalizer is ill-defined"
    end
  end
  @assert all(i > 0 for i in q) "Projection map is not surjective"
  FinFunction(q, codom(h))
end

colimit(span::Multispan{<:FinSet{Int}}) = composite_pushout(span)

""" Colimit of free diagram of FinSets.

See `CompositePushout` for a very similar construction.
"""
struct FinSetFreeDiagramColimit{Ob<:FinSet, Diagram<:FreeDiagram{Ob},
                                Cocone<:Multicospan{Ob}, Coprod<:Coproduct{Ob},
                                Proj<:FinFunction} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  proj::Proj # Projection for the "multi-coequalizer" in general formula.
end

function colimit(d::FreeDiagram{<:FinSet{Int}})
  # Uses the general formula for colimits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.2.16).
  coprod = coproduct(ob(d))
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for e in edges(d)
    s, t, h = src(d,e), tgt(d,e), hom(d,e)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  m = length(roots)
  π = FinFunction([ searchsortedfirst(roots, r) for r in h ], m)
  cocone = Multicospan(FinSet(m), [ compose(ιs[i],π) for i in vertices(d) ])
  FinSetFreeDiagramColimit(d, cocone, coprod, π)
end

function universal(colim::FinSetFreeDiagramColimit,
                   cocone::Multicospan{<:FinSet{Int}})
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end

end

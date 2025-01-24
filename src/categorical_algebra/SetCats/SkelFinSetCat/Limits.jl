
using ....Theories: dom, codom, id, compose, ⋅
using ....BasicSets, ...Cats 
import ...Cats: limit, universal
using ..FinSetCats: FinSetCompositeLimit

limit(Xs::EmptyDiagram{<:FinSet{Int}}) = Limit(Xs, SMultispan{0}(FinSet(1)))

universal(lim::Limit{<:FinSet{Int},<:EmptyDiagram}, cone::SMultispan{0}) =
  ConstantFunction(1, apex(cone), FinSet(1))

limit(Xs::SingletonDiagram{<:FinSet{Int}}) = limit(Xs, SpecializeLimit())

function limit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::Limit{<:FinSet{Int},<:ObjectPair}, cone::Span)
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

function universal(lim::Limit{<:FinSet{Int},<:DiscreteDiagram}, cone::Multispan)
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

function universal(lim::Limit{<:FinSet{Int},<:ParallelMorphisms},
                   cone::SMultispan{1})
  ι = collect(incl(lim))
  h = only(cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end


limit(d::FreeDiagram{<:FinSet{Int}}) = limit(FinDomFunctor(d))

function limit(F::Functor{<:FinCat{Int},<:TypeCat{<:FinSet{Int}}})
  # Uses the general formula for limits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.1.22 / Equation 5.16). This method is simple and direct,
  # but extremely inefficient!
  J = dom(F)
  prod = product(map(x -> ob_map(F, x), ob_generators(J)))
  n, πs = length(ob(prod)), legs(prod)
  ι = FinFunction(filter(1:n) do i
    all(hom_generators(J)) do f
      s, t, h = dom(J, f), codom(J, f), hom_map(F, f)
      h(πs[s](i)) == πs[t](i)
    end
  end, n)
  cone = Multispan(dom(ι), map(x -> ι⋅πs[x], ob_generators(J)))
  FinSetCompositeLimit(F, cone, prod, ι)
end

function universal(lim::FinSetCompositeLimit, cone::Multispan{<:FinSet{Int}})
  ι = collect(lim.incl)
  h = universal(lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)],
              apex(cone), ob(lim))
end

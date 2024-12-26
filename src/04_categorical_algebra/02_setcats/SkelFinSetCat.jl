module SkelFinSetCat 
export SkelFinSet

using DataStructures, StructEquality
using GATlab
using ....Theories
using ....BasicSets
using ...Cats


""" 
Skeleton of category of sets and functions. Objects are {1,2,...,n} for some 
n ∈ ℕ, represented as `FinSetInt`. Morphisms are `SetFunctions` whose domain 
and codomain are `FinSet(FinSetInt(n::Int))`.
"""
@struct_hash_equal struct SkelFinSet end

############
# Category #
############

@instance ThCategory{FinSetInt, FinFunction} [model::SkelFinSet] begin
  dom(f::FinFunction)::FinSetInt = getvalue(dom(f))

  codom(f::FinFunction)::FinSetInt = getvalue(codom(f))

  id(A::FinSetInt)::FinFunction = SetFunction(FinSet(A)) # identity function

  function compose(f::FinFunction, g::FinFunction)::FinFunction
    codom[model](f) == dom[model](g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end
end

@instance ThCategoryExplicitSets{FinSetInt, FinFunction, AbsSet
                                } [model::SkelFinSet] begin
  ob_set() = SetOb(FinSetInt)
  hom_set() = SetOb(FinFunction)
end

##########
# Limits #
##########

@instance ThCategoryWithTerminal{FinSetInt, FinFunction, AbsSet, AbsLimit, 
                                 Multispan, EmptyDiagram,
                                } [model::SkelFinSet] begin 
  ob(x::AbsLimit) = ob(x) # always use dispatch
  apex(x::Multispan) = apex(x) # always use dispatch

  limit(::EmptyDiagram)::AbsLimit = 
    TerminalLimit{FinSetInt,FinFunction}(FinSetInt(1))

  universal(::AbsLimit, ::EmptyDiagram, a::Multispan) = 
    FinFunction(ConstantFunction(1, FinSet(apex[model](a)), FinSet(1)))
end


@instance ThCategoryUnbiasedProducts{FinSetInt, FinFunction, AbsSet, AbsLimit, 
    Multispan, EmptyDiagram,DiscreteDiagram} [model::SkelFinSet] begin

  function limit(Xs::DiscreteDiagram)::AbsLimit
    ns = length.(Xs)
    indices = CartesianIndices(Tuple(ns))
    n = prod(Vector{Int}(ns))
    πs = [SetFunction(i -> indices[i][j], FinSet(n), FinSet(ns[j])) 
          for j in 1:length(ns)]
    LimitCone(Multispan(FinSetInt(n), πs, FinSetInt.(ns)), 
              FreeDiagram(Xs))
  end

  function universal(p::AbsLimit, ::DiscreteDiagram, span::Multispan)
    ns = length.(codom.(span))
    indices = LinearIndices(Tuple(ns))
    v = map(apex(span)) do i 
      indices[(f(i) for f in span)...]
    end
    FinFunction(v, FinSet(apex(p)))
  end
end

@instance ThCategoryWithEqualizers{FinSetInt, FinFunction, AbsSet, AbsLimit, 
    Multispan, EmptyDiagram,DiscreteDiagram,ParallelMorphisms} [model::SkelFinSet] begin

  function limit(para::ParallelMorphisms)
    @assert !isempty(para)
    f1, frest = para[1], para[2:end]
    m = length(dom(para))
    eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
    LimitCone(Multispan(dom[model](eq), [eq]; cat=model), FreeDiagram(para))
  end 
  
  function universal(res::AbsLimit, ::ParallelMorphisms, span::Multispan)
    ι = collect(only(cone(res)))
    h = only(span)
    FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom[model](h)], 
                length(ι))
  end 

end

############
# Colimits #
############

@instance ThCategoryWithInitial{FinSetInt,FinFunction,AbsSet,AbsColimit,
    Multicospan, EmptyDiagram} [model::SkelFinSet] begin 

  ob(t::AbsColimit)::FinSetInt = ob(t)

  apex(t::Multicospan)::FinSetInt = t.apex

  colimit(::EmptyDiagram)::AbsColimit = 
    InitialColimit{FinSetInt,FinFunction}(FinSetInt(0))

  universal(::AbsColimit, ::EmptyDiagram, a::Multicospan) = 
    FinFunction(Int[], FinSet(apex[model](a)))
end

@instance ThCategoryUnbiasedCoproducts{FinSetInt,FinFunction,AbsSet,AbsColimit,
    Multicospan, EmptyDiagram, DiscreteDiagram} [model::SkelFinSet] begin

  function colimit(Xs::DiscreteDiagram)::AbsColimit
    ns = length.(Xs)
    n = sum(ns)
    offsets = [0,cumsum(ns)...]
    ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
    csp = Multicospan{FinSetInt, FinFunction}(FinSetInt(n), ιs, FinSetInt.(ns))
    ColimitCocone(csp, FreeDiagram(Xs))
  end

  function universal(::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    v = mapreduce(collect, vcat, cocone, init=Int[])
    FinFunction(v, FinSet(apex(cocone)))  
  end
end


@instance ThCategoryWithCoequalizers{FinSetInt, FinFunction, AbsSet, AbsColimit, 
    Multicospan, EmptyDiagram,DiscreteDiagram,ParallelMorphisms} [model::SkelFinSet] begin

  function colimit(para::ParallelMorphisms)
    emp = EmptyDiagram{impl_type(model, ThCategory, :Ob)}()
    isempty(para) && return colimit(emp) 
    f1, frest = para[1], para[2:end]
    m, n = length(dom(para)), length(codom(para))
    sets = IntDisjointSets(n)
    for i in 1:m
      for f in frest
        union!(sets, f1(i), f(i))
      end
    end
    q = quotient_projection(sets)
    ColimitCocone(Multicospan(codom[model](q), [q]; cat=model), FreeDiagram(para))
  end 
  
  function universal(res::AbsColimit, ::ParallelMorphisms, x::Multicospan)
    pass_to_quotient(only(cocone(res)), only(x))
  end 
end

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


end # module

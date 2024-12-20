module SkelFinSetCat 
export SkelFinSet

using StructEquality
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

@instance ThCategoryExplicitSets{FinSetInt, FinFunction, AbsSet} [model::SkelFinSet] begin
  @import Ob, Hom, id, compose, dom, codom, →, ⋅
  ob_set() = SetOb(FinSetInt)
  hom_set() = SetOb(FinFunction)
end


##########
# Limits #
##########

@instance ThCategoryWithTerminal{FinSetInt,FinFunction,TerminalLimit
                                } [model::SkelFinSet] begin 
  @import Ob, Hom, id, compose, dom, codom, →, ⋅, ◊

  terminal()::TerminalLimit = TerminalLimit{FinSetInt,FinFunction}(FinSetInt(1))

  ob(t::TerminalLimit)::FinSetInt = t.ob

  universal(::TerminalLimit, a::FinSetInt) = 
    FinFunction(ConstantFunction(1, FinSet(a), FinSet(1)))
    
end


@instance ThCategoryUnbiasedProducts{FinSetInt,SetFunction,TerminalLimit,
    DiscreteDiagram, Multispan,ProductLimit} [model::SkelFinSet] begin

  @import Ob, Hom, id, compose, dom, codom, →, ⋅, terminal, Terminal, ob, universal, ◊

  ap(s::Multispan)::FinSetInt = apex(s)

  ob(t::ProductLimit)::FinSetInt = getvalue(apex(t))

  function product(Xs::DiscreteDiagram)::ProductLimit
    ns = length.(Xs)
    indices = CartesianIndices(Tuple(ns))
    n = prod(ns)
    πs = [SetFunction(i -> indices[i][j], FinSet(n), FinSet(ns[j])) 
          for j in 1:length(ns)]
    ProductLimit(Multispan(FinSet(n), πs))
  end

  function universal(p::ProductLimit, span::Multispan)
    ns = length.(codom.(span))
    indices = LinearIndices(Tuple(ns))
    v = map(apex(span)) do i 
      indices[(f(i) for f in span)...]
    end
    FinFunction(v, apex(p))  
  end
end

############
# Colimits #
############

@instance ThCategoryWithInitial{FinSetInt,FinFunction,InitialColimit
                                } [model::SkelFinSet] begin 
  @import Ob, Hom, id, compose, dom, codom, →, ⋅, □

  initial()::InitialColimit = InitialColimit{FinSetInt,FinFunction}(FinSetInt(0))
  ob(t::InitialColimit)::FinSetInt = t.ob
  universal(::InitialColimit, a::FinSetInt) = FinDomFunction(eltype(a)[], FinSet(a))
end

@instance ThCategoryUnbiasedCoproducts{AbsSet,SetFunction,InitialColimit,
    DiscreteDiagram, Multicospan, CoproductColimit} [model::SkelFinSet] begin

  @import Ob, Hom, id, compose, dom, codom, →, ⋅, initial, Initial, ob, universal, □

  ap(s::Multicospan)::FinSetInt = apex(s)

  ob(t::CoproductColimit)::FinSetInt = getvalue(apex(t))

  function coproduct(Xs::DiscreteDiagram)::CoproductColimit
    ns = length.(Xs)
    n = sum(ns)
    offsets = [0,cumsum(ns)...]
    ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
    CoproductColimit(Multicospan(FinSet(n), ιs))
  end

  function universal(colim::CoproductColimit, cocone::Multicospan)
    v = mapreduce(collect, vcat, cocone, init=Int[])
    FinDomFunction(v, apex(cocone))  
  end
end



end # module

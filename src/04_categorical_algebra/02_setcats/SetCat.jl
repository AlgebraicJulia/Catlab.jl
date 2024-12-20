module SetCLimits 

export SetC

using StructEquality
using GATlab

using ....Theories
using ....BasicSets: AbsSet, FinSet, ConstantFunction, SetFunction, ProdSet, 
  SetOb, FinDomFunction, ProdFinSet, FinFunction, FinSetInt
using ...Cats


""" Category of sets and functions """
@struct_hash_equal struct SetC end

@instance ThCategory{AbsSet, SetFunction} [model::SetC] begin
  dom(f::SetFunction)::AbsSet = dom(f)
  codom(f::SetFunction)::AbsSet = codom(f)

  id(A::AbsSet)::SetFunction = SetFunction(A) # identity function

  function compose(f::SetFunction, g::SetFunction)::SetFunction
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end
end

@instance ThCategoryWithTerminal{AbsSet,SetFunction,TerminalLimit
                                } [model::SetC] begin 
  @import Ob, Hom, id, compose, dom, codom, →, ⋅, ◊

  terminal()::TerminalLimit = TerminalLimit{AbsSet,SetFunction}(FinSet(nothing))
  ob(t::TerminalLimit)::AbsSet = t.ob
  delete(::TerminalLimit, a::AbsSet) = 
    SetFunction(ConstantFunction(nothing, a, FinSet(nothing)))
    
end

@instance ThCategoryWithInitial{AbsSet,SetFunction,InitialColimit
                                } [model::SetC] begin 
  @import Ob, Hom, id, compose, dom, codom, →, ⋅, □

  initial()::InitialColimit = InitialColimit{AbsSet,SetFunction}(FinSet(Set{Union{}}()))
  ob(t::InitialColimit)::AbsSet = t.ob
  create(::InitialColimit, a::AbsSet) = FinDomFunction(Dict(), a)
end



@instance ThCategoryUnbiasedProducts{AbsSet,SetFunction,TerminalLimit,
    DiscreteDiagram, Multispan,ProductLimit} [model::SetC] begin

  @import Ob, Hom, id, compose, dom, codom, →, ⋅, terminal, Terminal, ob, delete, ◊

  ap(s::Multispan)::AbsSet = apex(s)

  ob(t::ProductLimit)::AbsSet = t.ob

  function product(a::DiscreteDiagram)::ProductLimit
    X = if all(s -> s isa FinSet, a)
      FinSet(ProdFinSet(collect(a)))
    else 
      SetOb(ProdSet(collect(a)))
    end
    πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(a)]
    ProductLimit(Multispan(X, πs))
  end

  function universal(p::ProductLimit, span::Multispan)
    Xs = feet(p)
    if !all(X -> X isa FinSet, Xs)
      @assert length(cone(p)) == length(span)
      fs = Tuple(legs(span))
      SetFunction(x -> map(f -> f(x), fs), apex(span), ob(p))
    else
      ns = length.(codom.(span))
      indices = LinearIndices(Tuple(ns))
      v = map(apex(cone)) do i 
        indices[(f(i) for f in span)...]
      end
      FinFunction(v, apex(res))  
    end
  end
end


end # module
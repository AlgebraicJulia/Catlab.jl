module VarFnLimits 

using StructEquality, DataStructures
using GATlab 
using .....BasicSets 
using ....Cats, ...SetCats
using ..VarFunctions

@instance ThCategoryUnbiasedCoproducts{FinSetInt, SetFunction, AbsSet,
  AbsColimit, Multicospan, DiscreteDiagram} [model::SkelKleisli{T}] where T begin 

  function colimit(d::DiscreteDiagram)::AbsColimit
    csp = fmap(cocone(colimit[SkelFinSet()](d)), identity, x->pure(x,T), 
               FinSetInt, SetFunction)
    ColimitCocone(csp, FreeDiagram(d))
  end  
  function universal(::AbsColimit,::DiscreteDiagram, cocone::Multicospan)
    v = mapreduce(collect, vcat, cocone, init=Union{Left{Int},Right{T}}[])
    FinDomFunction(v, either(FinSet(apex(cocone)), SetOb(T)))  
  end
end

@instance ThCategoryWithCoequalizers{FinSetInt, SetFunction, AbsSet, AbsColimit, 
    Multicospan,ParallelMorphisms} [model::SkelKleisli{T}] where T begin

  function colimit(para::ParallelMorphisms)
    emp = EmptyDiagram{impl_type(model, ThCategory, :Ob)}()
    isempty(para) && return colimit(emp) 
    sets = DisjointSets{Union{Left{Int},Right{T}}}(collect(Left.(codom(para))))
    for i in dom(para)
      f₁ᵢ, f_restᵢ... = fs = map.(para, i)
      rights = unique(collect(filter(x->x isa Right, fs)))
      length(rights) > 1 && error("Bad map for $i: $([f₁ᵢ, f_restᵢ...])")
      if length(rights) == 1
        r = only(rights)
        r ∉ sets && push!(sets, r)
      end
      for fᵢ in f_restᵢ 
        union!(sets, f₁ᵢ, fᵢ)
      end
    end
    q = quotient_projection(sets, length(codom(para)), T)
    cod = codom[model](q)
    ColimitCocone(Multicospan(cod, [q]; cat=model), FreeDiagram(para))
  end 
  
  function universal(res::AbsColimit, ::ParallelMorphisms, x::Multicospan)
    pass_to_quotient(only(cocone(res)), only(x))
  end 
end

""" Create projection map π: X → X/∼ from partition of X.

When we merge Left and Right values, take a Right value if possible. This means 
that the "real root" of a given equivalence class is not the one that comes with
the data structure naturally.

If there is more than one Right value in the equivalence class, throw an error.
"""
function quotient_projection(sets::DisjointSets, nₓ::Int, T::Type)
  vec = map(collect(sets)[1:nₓ]) do cod_elem 
    fake_root = find_root!(sets, cod_elem)
    Rs = filter(sets) do s 
      s isa Right && find_root!(sets, s) == fake_root 
    end
    length(Rs) > 1 && error("Ill-defined quotient: merging $(getvalue.(Rs))")
    length(Rs) == 1 ? only(Rs) : fake_root
  end
  left_elems = sort(collect(filter(x -> x isa Left, unique(vec))))
  left_elem_dict = Dict(y =>Left(x) for (x,y) in enumerate(left_elems))
  FinDomFunction([v isa Right ? v : left_elem_dict[v] for v in vec], 
                 either(FinSet(length(left_elems)), SetOb(T)))
end


""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.

Left values are variables. Quotient is only ill-defined if Right values conflict.
"""
function pass_to_quotient(π::Fin_FinDom, h::Fin_FinDom)
  q = Vector{eltype(codom(h))}(fill(Left(0), length(left(getvalue(codom(π))))))
  for i in dom(h)
    j = π(i)
    j isa Right && continue
    j = getvalue(j)
    if q[j] == Left(0)
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined $(q[j]) ≠ $(h(i))")
    end
  end
  any(==(Left(0)), q) && error("Projection map is not surjective")
  FinDomFunction(q, codom(h))
end


@instance ThCategoryWithPushouts{FinSetInt, SetFunction, AbsSet,
  AbsColimit, Multicospan, Multispan} [model::SkelKleisli{T}] where T begin 

  function colimit(spn::Multispan)::AbsColimit
    composite_colimit(CatWithCoequalizers(model), spn)
  end

  function universal(res::AbsColimit,::Multispan, x::Multicospan)
    composite_universal(CatWithCoequalizers(model), res, x)
  end

end

end # module

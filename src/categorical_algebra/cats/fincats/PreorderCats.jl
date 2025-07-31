module PreorderCats 

export PreorderFinCat

using StructEquality

using GATlab 

using ......Graphs
using ......BasicSets: FinSet, SetOb
using ...Paths: Path
using ..FinCats: ThFinCat
import ..FinCats: FinCat, decompose

"""
A case where generators and morphisms share the same Julia type, and where morphisms are not mere paths of generators.

E.g. for A ≤ B ≤ C, we have `gens = [A,B,C]` and `gendict=Dict(A=>1,B=>2,C=>3)` 
and `rel = Set([1=>1,1=>2,1=>3,2=>2,2=>3,3=>3])`.
"""
@struct_hash_equal struct PreorderFinCat{Ob}
  gens::FinSet
  genvec::Vector{Ob}
  gendict::Dict{Ob,Int}
  rel::Set{Pair{Int,Int}}
  function PreorderFinCat(p::AbstractVector{Pair{Ob,Ob}}; vals=nothing) where Ob
    # compute transitive closure
    vals = isnothing(vals) ? FinSet(Set([first.(p); last.(p)])) : vals
    genvec = sort(collect(vals))
    gendict = Dict(v => i for (i, v) in enumerate(genvec))
    m(f) = [gendict[f(x)] for x in p]
    G = Graph(length(vals))
    add_edges!(G, m(first), m(last))
    ps = enumerate_paths(G)
    r = [s=>t for (s,t,e) in zip(ps[:src], ps[:tgt], ps[:eprops]) 
         if s==t || !isempty(e)]
    new{Ob}(vals, genvec, gendict, Set(r))
  end
end

PreorderFinCat(p::AbstractVector{Tuple{Ob,Ob}}; vals=nothing) where Ob = 
  PreorderFinCat([x=>y for (x,y) in p]; vals)

PreorderFinCat(p::T, q::T; vals=nothing) where {Ob, T<:AbstractVector{Ob}} = 
  PreorderFinCat(collect(zip(p,q)); vals)

@instance ThFinCat{Ob, Pair{Int,Int}, Pair{Int,Int}, 
                  } [model::PreorderFinCat{Ob}] where {Ob} begin
  dom(f::Pair{Int,Int})::Ob = model.gens[first(f)]

  codom(f::Pair{Int,Int})::Ob = model.gens[last(f)]

  src(f::Pair{Int,Int})::Ob = model.gens[first(f)]

  tgt(f::Pair{Int,Int})::Ob = model.gens[last(f)]

  id(x::Ob) = (model.gendict[x] => model.gendict[x])
  
  compose(f::Pair{Int,Int}, g::Pair{Int,Int})::Pair{Int,Int} = first(f) => last(g)

  ob_set()::SetOb = SetOb(getvalue(model.gens))

  gen_set()::FinSet = FinSet(model.rel)
  
  hom_set()::SetOb = SetOb(model.rel)

  to_hom(gen::Pair{Int,Int})::Pair{Int,Int} = gen
end

decompose(::PreorderFinCat, f::Pair{Int,Int}) = Path([f], f[1], f[2])

end # module

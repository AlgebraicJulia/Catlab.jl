
"""
In order to avoid type ambiguities, generators and morphisms need different
types. 
"""
@struct_hash_equal struct PreorderFinCat{Ob} <: FinCatImpl{Ob,Pair{Int,Int},Pair{Int,Int}}
  gens::Vector{Ob}
  gendict::Dict{Ob,Int}
  rel::Set{Pair{Int,Int}}
  function PreorderFinCat(p::AbstractVector{Pair{Ob,Ob}}; vals=nothing) where Ob
    # compute transitive closure
    vals = isnothing(vals) ? unique([first.(p); last.(p)]) : vals
    valdict = Dict(v=>i for (i,v) in enumerate(vals))
    m(f) = [valdict[f(x)] for x in p]
    G = Graph(length(vals))
    add_edges!(G, m(first), m(last))
    ps = enumerate_paths(G)
    r = [s=>t for (s,t,e) in zip(ps[:src], ps[:tgt], ps[:eprops]) 
         if s==t || !isempty(e)]
    new{Ob}(vals, valdict, Set(r))
  end
end

PreorderFinCat(p::AbstractVector{Tuple{Ob,Ob}}; vals=nothing) where Ob = 
  PreorderFinCat([x=>y for (x,y) in p]; vals)

PreorderFinCat(p::T, q::T; vals=nothing) where {Ob, T<:AbstractVector{Ob}} = 
  PreorderFinCat(collect(zip(p,q)); vals)

@instance ThFinCat{Ob, Pair{Int,Int}, Pair{Int,Int}, Any} [model::PreorderFinCat{Ob}
                                      ] where {Ob} begin
  dom(f::Pair{Int,Int})::Ob = model.gens[first(f)]

  codom(f::Pair{Int,Int})::Ob = model.gens[last(f)]

  id(x::Ob)::Pair{Int,Int} = let i = model.gens[x]; i => i end

  compose(f::Pair{Int,Int}, g::Pair{Int,Int})::Pair{Int,Int} = (f[1]=> g[2])

  singleton(f::Pair{Int,Int})::Pair{Int,Int} = f

  ob_generators() = model.gens

  hom_generators() = collect(model.rel)
end

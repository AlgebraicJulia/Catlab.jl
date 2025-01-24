import ...Cats: colimit, universal

function colimit(d::BipartiteFreeDiagram{<:VarSet{T}}) where T
  n₁,n₂ = [nparts(d,x) for x in [:V₁,:V₂]]
  # Get list of variables across all ACSets in diagram
  n_vars = [x.n for x in vcat(d[:ob₁], d[:ob₂])]
  cs = cumsum(n_vars) |> collect
  var_indices = [(a+1):b for (a,b) in zip([0,cs...],cs)]
  vars = IntDisjointSets(sum(n_vars))

  concrete = Dict{Int,T}() # map vars to concrete attributes, if any

  # quotient variable set using homs + bind vars to concrete attributes
  for (h, s, t) in zip(d[:hom], d[:src], d[:tgt])
    for (local_src_var, local_tgt) in enumerate(collect(h))
      if local_tgt isa AttrVar 
        union!(vars, var_indices[s][local_src_var], 
                     var_indices[t+n₁][local_tgt.val])
      else
        concrete[var_indices[s][local_src_var]] = local_tgt
      end 
    end
  end

  concretes = Dict([find_root!(vars, k)=>v for (k,v) in collect(concrete)])
  roots = unique(filter(r->!haskey(concretes,r), 
                        [find_root!(vars, i) for i in 1:length(vars)]))
  n_var = VarSet{T}(length(roots)) # number of resulting variables
  # Construct maps into apex
  csp = Multicospan(n_var, map(var_indices[(1:n₂).+n₁]) do v_is 
    VarFunction{T}(map(v_is) do v_i 
      r = find_root!(vars, v_i)
      haskey(concretes,r) ? concretes[r] : AttrVar(findfirst(==(r), roots))
    end, FinSet(n_var.n))
  end)
  # Cocone diagram
  return Colimit(d, csp)
end 

# FIXME: Handle more specific diagrams? Now only VarSet colimits will be bipartite
function universal(lim::BipartiteColimit{<:VarSet{T}}, cocone::Multicospan) where {T}
  VarFunction{T}(map(collect(apex(lim))) do p 
    for (l, csp) in zip(legs(lim), cocone)
      pre = preimage(l, p) # find some colimit leg which maps onto this part
      if !isempty(pre)
        return csp(AttrVar(first(pre))) # pick arbitrary elem and apply cocone map
      end 
    end 
    error("Colimit legs should be jointly surjective")
  end, FinSet(apex(cocone).n))
end


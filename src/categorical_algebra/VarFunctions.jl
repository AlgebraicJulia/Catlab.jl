module VarFunctions 
export VarSet, VarFunction, AbsVarFunction, LooseVarFunction

using StructEquality
using DataStructures: OrderedDict, IntDisjointSets, union!, find_root!

using ACSets

import ....Theories: dom, codom, compose, id, ⋅
using ....BasicSets
import ....BasicSets: FinFunction, SetOb, FinSet, is_monic, force, preimage, is_epic

using ..Limits, ..Subobjects, ..FreeDiagrams
import ..FinSetCats: predicate
using ..Limits: BipartiteColimit
import ..Limits: colimit, universal
using ..Subobjects: SubobjectHom

# Variable component maps 
#########################
"""
Control dispatch in the category of VarFunctions
"""
@struct_hash_equal struct VarSet{T}
  n::Int 
end
VarSet(i::Int) = VarSet{Union{}}(i)
SetOb(s::VarSet{Union{}}) = FinSet(s)
SetOb(s::VarSet{T}) where T = TypeSet{Union{AttrVar,T}}()
FinSet(s::VarSet) = FinSet(s.n) #Note this throws away `T`, most accurate when thinking about tight `VarFunction`s.
"""
The iterable part of a varset is its collection of `AttrVar`s.
"""
Base.iterate(set::VarSet{T}, args...) where T = iterate(AttrVar.(1:set.n), args...)
Base.length(set::VarSet{T}) where T = set.n
Base.in(elem, set::VarSet{T}) where T = in(elem, 1:set.n)
Base.eltype(set::VarSet{T}) where T = Union{AttrVar,T}

function predicate(A::SubobjectHom{<:VarSet}) 
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    fx = f(x)
    if fx isa AttrVar
      pred[fx.val] = true
    end
  end
  pred
end

abstract type AbsVarFunction{T} end # either VarFunction or LooseVarFunction
"""
Data type for a morphism of VarSet{T}s. Note we can equivalently view these 
as morphisms [n]+T -> [m]+T fixing T or as morphisms [n] -> [m]+T, in the typical
Kleisli category yoga. 

Currently, domains are treated as VarSets. The codom field is treated as a FinSet{Int}.
Note that the codom accessor gives a VarSet while the codom field is just that VarSet's 
FinSet of AttrVars.
This could be generalized to being FinSet{Symbol} to allow for
symbolic attributes. (Likewise, AttrVars will have to wrap Any rather than Int)
"""
@struct_hash_equal struct VarFunction{T} <: AbsVarFunction{T}
  fun::FinDomFunction
  codom::FinSet
  function VarFunction{T}(f,cod::FinSet) where T
    all(e-> (e isa AttrVar && e.val ∈ cod) || e isa T, f) || error("Codom error: $f $T $cod")
    return new(FinDomFunction(Vector{Union{AttrVar,T}}(f)), cod)
  end 
end
VarFunction(f::AbstractVector{Int},cod::Int) = VarFunction(FinFunction(f,cod))
VarFunction(f::FinDomFunction) = VarFunction{Union{}}(AttrVar.(collect(f)),codom(f))
VarFunction{T}(f::FinDomFunction,cod::FinSet) where T = VarFunction{T}(collect(f),cod)
FinFunction(f::VarFunction{T}) where T = FinFunction(
  [f(i) isa AttrVar ? f(i).val : error("Cannot cast to FinFunction") 
   for i in dom(f)], f.codom)
FinDomFunction(f::VarFunction{T}) where T = f.fun
Base.length(f::AbsVarFunction{T}) where T = length(collect(f.fun))
Base.collect(f::AbsVarFunction{T}) where T = collect(f.fun)
 
(f::VarFunction{T})(v::T) where T = v 
(f::AbsVarFunction{T})(v::AttrVar) where T = f.fun(v.val) 

#XX if a VarSet could contain an arbitrary FinSet of variables this
#   wouldn't need to be so violent
dom(f::AbsVarFunction{T}) where T = VarSet{T}(length(collect(f.fun)))
codom(f::VarFunction{T}) where T = VarSet{T}(length(f.codom))
id(s::VarSet{T}) where T = VarFunction{T}(AttrVar.(1:s.n), FinSet(s.n))
function is_monic(f::VarFunction) 
  if any(x-> !(x isa AttrVar), collect(f.fun)) return false end 
  vals = [v.val for v in collect(f.fun)]
  return length(vals) == length(unique(vals))
end
is_epic(f::VarFunction) = AttrVar.(f.codom) ⊆ collect(f) #XXX: tested?

compose(::IdentityFunction{TypeSet{T}}, f::AbsVarFunction{T}) where T = f
compose(f::VarFunction{T}, ::IdentityFunction{TypeSet{T}}) where T = f

FinDomFunction(f::Function, dom, codom::VarSet{T}) where T =
  SetFunctionCallable(f, FinSet(dom), SetOb(codom))

"""Kleisi composition of [n]->T+[m] and [m]->T'+[p], yielding a [n]->T'+[p]"""
compose(f::VarFunction{T},g::VarFunction{T}) where {T} =
  VarFunction{T}([elem isa AttrVar ? g.fun(elem.val) : elem 
                  for elem in collect(f)], g.codom)


"""Compose [n]->[m]+T with [m]->[p], yielding a [n]->T+[p]"""
compose(f::VarFunction{T}, g::FinFunction) where T =
  VarFunction{T}([elem isa AttrVar ? AttrVar(g(elem.val)) : elem 
                  for elem in collect(f)], g.codom)

"""Compose [n]->[m] with [m]->[p]+T, yielding a [n]->T+[p]"""
compose(f::FinFunction,g::VarFunction{T}) where T =
  VarFunction{T}(compose(f,g.fun), g.codom)

preimage(f::VarFunction{T}, v::AttrVar) where T = preimage(f.fun, v)
preimage(f::VarFunction{T}, v::T) where T = preimage(f.fun, v)
force(f::VarFunction{T}) where T = f

@struct_hash_equal struct LooseVarFunction{T,T′}  <: AbsVarFunction{T}
  fun::FinDomFunction
  loose::SetFunction
  codom::FinSet
  function LooseVarFunction{T,T′}(f,loose,cod) where {T, T′}
    all(e-> (e isa AttrVar && e.val ∈ cod) || e isa T′, f) || error("Codomain error: $f")
    return new(FinDomFunction(Vector{Union{AttrVar,T′}}(f)), loose, cod)
  end
end
LooseVarFunction{T,T′}(f, loose::F, cod) where {T,T′,F<:Function} = 
  LooseVarFunction{T,T′}(f, SetFunction(loose,TypeSet(T),TypeSet(T′)),cod)

(f::LooseVarFunction{T})(v::T) where T = f.loose(v)
codom(f::LooseVarFunction{T,T′}) where {T,T′} = VarSet{T′}(length(f.codom))
compose(f::LooseVarFunction{<:Any,T′}, ::IdentityFunction{TypeSet{T′}}) where {T′} = f

compose(f::LooseVarFunction{T,T′},g::LooseVarFunction{T′,T′′}) where {T, T′,T′′} =
  LooseVarFunction{T,T′′}([elem isa AttrVar ? g.fun(elem.val) : g.loose(elem) 
                           for elem in collect(f)], f.loose⋅g.loose, g.codom)

⋅(f::AbsVarFunction, g::AbsVarFunction) = compose(f,g)
force(f::LooseVarFunction{T,T′}) where {T,T′} = f


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


end # module

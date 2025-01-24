using StructEquality

import ACSets: ACSet
import ...Cats: FinDomFunctor

# Categories interop
####################

# ACSets as set-valued FinDomFunctors.

# TODO: We should wrap `SchemaDescType` instead of creating a presentation.
const ACSetDomCat = FinCats.FinCatPresentation{
  Symbol, Union{FreeSchema.Ob,FreeSchema.AttrType},
  Union{FreeSchema.Hom,FreeSchema.Attr,FreeSchema.AttrType}}

""" Wrapper type to interpret attributed C-set as a functor.
"""
@struct_hash_equal struct ACSetFunctor{ACS<:ACSet} <:
    Functor{ACSetDomCat,
            TypeCat{Union{FinSet,VarSet},
                    Union{VarFunction,FinDomFunction{Int}}}}
  acset::ACS
end
FinDomFunctor(X::ACSet) = ACSetFunctor(X)
ACSet(X::ACSetFunctor) = X.acset

function hasvar(X::ACSet,x) 
  s = acset_schema(X)
  (x∈ attrs(acset_schema(X),just_names=true) && hasvar(X,codom(s,x))) || 
  x∈attrtypes(acset_schema(X)) && nparts(X,x)>0
end
hasvar(X::ACSet) = any(o->hasvar(X,o), attrtypes(acset_schema(X)))
hasvar(X::ACSetFunctor,x) = hasvar(X.acset,x)
hasvar(X::ACSetFunctor) = hasvar(X.acset)


dom(F::ACSetFunctor) = FinCat(Presentation(ACSet(F)))

#not clear this couldn't just always give the Vars
function codom(F::ACSetFunctor)
  hasvar(F) ? TypeCat{Union{SetOb,VarSet},Union{FinDomFunction{Int},VarFunction}}() :
    TypeCat{SetOb,FinDomFunction{Int}}()
end

Functors.do_ob_map(F::ACSetFunctor, x) = 
  (hasvar(F,functor_key(x)) ? VarSet : SetOb)(F.acset, functor_key(x))
Functors.do_hom_map(F::ACSetFunctor, f) =  
  (hasvar(F,functor_key(f)) ? VarFunction : FinFunction)(F.acset, functor_key(f))

functor_key(x) = x
functor_key(expr::GATExpr{:generator}) = first(expr)

# Set-valued FinDomFunctors as ACSets.
(T::Type{ACS})(F::Diagram) where ACS <: ACSet = F |> diagram |> T
function (::Type{ACS})(F::FinDomFunctor) where ACS <: ACSet
  X = if ACS isa UnionAll
    pres = presentation(dom(F))
    ACS{(strip_attrvars(eltype(ob_map(F, c))) for c in generators(pres, :AttrType))...}()
  else
    ACS()
  end
  copy_parts!(X, F)
  return X
end
strip_attrvars(T) = T
strip_attrvars(::Type{Union{AttrVar, T}}) where T = T

""" Copy parts from a set-valued `FinDomFunctor` to an `ACSet`.
"""
function ACSetInterface.copy_parts!(X::ACSet, F::FinDomFunctor)
  pres = presentation(dom(F))
  added = Dict(Iterators.map(generators(pres, :Ob)) do c
    c = nameof(c)
    c => add_parts!(X, c, length(ob_map(F, c)::FinSet{Int}))
  end)
  for f in generators(pres, :Hom)
    dom_parts, codom_parts = added[nameof(dom(f))], added[nameof(codom(f))]
    set_subpart!(X, dom_parts, nameof(f), codom_parts[collect(hom_map(F, f))])
  end
  for f in generators(pres, :Attr)
    cd = nameof(codom(f))
    dom_parts = added[nameof(dom(f))]
    F_of_f = collect(hom_map(F,f))
    n_attrvars_present = nparts(X, cd)
    n_attrvars_needed = maximum(map(x->x.val,filter(x->x isa AttrVar,F_of_f)),init=0)
    add_parts!(X,cd,n_attrvars_needed-n_attrvars_present)
    set_subpart!(X, dom_parts, nameof(f), F_of_f)
  end
  added
end


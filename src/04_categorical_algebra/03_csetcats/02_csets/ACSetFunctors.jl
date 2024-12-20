module ACSetFunctors 

export ACSetFunctor

using StructEquality

using GATlab, ACSets
import GATlab: getvalue
import ACSets: ACSet
using ACSets.DenseACSets: attrtype_type

using .....BasicSets: SetOb, SetFunction
using ....Cats: Category, FinCat, Cat, obtype, homtype, TypeCat,
               ob_generators, hom_generators, gentype, ThFinDomFunctor
import ....Cats: FinDomFunctor
using ..CSets: ACSetCategory, get_ob, get_hom
using ..CodomsOfACSet: CodomOfACSet

""" Wrapper type to interpret attributed C-set as a functor.
"""
@struct_hash_equal struct ACSetFunctor{ACS<:ACSet, Ob, Hom}
  acset::ACS
  cod::ACSetCategory
  function ACSetFunctor(x::T, c::ACSetCategory) where {T<:ACSet}
    new{T, Union{obtype(c), attrtype_type(c)},
           Union{homtype(c), attrtype(c)}}(x, c)
  end
end

# Accessors
###########
getvalue(f::ACSetFunctor) = f.acset

getcategory(f::ACSetFunctor) = f.cod

ACSet(X::ACSetFunctor) = X.acset # synonym for getvalue

# Other methods
###############

""" Inverse to constructing an ACSetFunctor """
function (::Type{ACS})(F::T) where {ACS <: ACSet, T<:ACSetFunctor}
  X = if ACS isa UnionAll
    pres = presentation(dom(F))
    ACS{(strip_attrvars(eltype(ob_map(F, c))) for c in generators(pres, :AttrType))...}()
  else
    ACS()
  end
  copy_parts!(X, F)
  return X
end


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

# FinDomFunctor interface
#########################

@instance ThFinDomFunctor{GATExpr{:generator}, Ob, GATExpr, Hom,
                          GATExpr{:generator}, FinCat, Category
                          } [model::ACSetFunctor{ACS, Ob, Hom} 
                            ] where {ACS, Ob, Hom} begin 

  dom() = FinCat(Presentation(getvalue(model)))

  codom() = Category(TypeCat(CodomOfACSet(model.cod)))

  ob_map(x::GATExpr{:generator})::Ob = 
    get_ob(model.cod, getvalue(model), nameof(x))  
  #SetOb(getvalue(model), x, getcategory(model))

  gen_map(f::GATExpr{:generator})::Hom = 
    get_hom(model.cod, getvalue(model), nameof(f), 
            ThFinDomFunctor.ob_map[model](dom(f)), 
            ThFinDomFunctor.ob_map[model](codom(f))) 
            #SetFunction(getvalue(model), f, getcategory(model))
end

# Constructors
###############

FinDomFunctor(acs::ACSet, C::Category) = FinDomFunctor(acs, getvalue(C))

FinDomFunctor(acs::ACSet, C::TypeCat) = FinDomFunctor(acs, getvalue(C))

# FinDomFunctor(acs::ACSet, C::CatOfACSet) = FinDomFunctor(acs, getvalue(C))

FinDomFunctor(acs::ACSet, C::ACSetCategory) = FinDomFunctor(ACSetFunctor(acs, C))

end #module

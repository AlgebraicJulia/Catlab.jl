module ACSetFunctors 

export ACSetFunctor

using StructEquality

using GATlab, ACSets
import ACSets: ACSet
using ACSets.DenseACSets: attrtype_type

using .....BasicSets
using ....Cats
import ....Cats: FinDomFunctor
using ...Pointwise, ..CSets

""" Wrapper type to interpret attributed C-set as a functor.
"""
@struct_hash_equal struct ACSetFunctor{ACS<:ACSet, Ob, Hom}
  acset::ACS
  cod::ACSetCategory
  function ACSetFunctor(x::T, c::ACSetCategory) where {T<:ACSet}
    S = acset_schema(c)
    O,H,AT,Op,A = impl_type.(Ref(c), [:Ob, :Hom, :AttrType,:Op, :Attr])
    Op′, AT′, A′ = [Tagged(Dict{Symbol,Type}(a=>X for a in attrtypes(S)))   
                    for X in [Op, AT, A]]
    new{T, Union{O, AT′}, Union{H, Op′, A′}}(x, c)
  end
end

# Accessors
###########
GATlab.getvalue(f::ACSetFunctor) = f.acset

getcategory(f::ACSetFunctor) = f.cod

ACSet(X::ACSetFunctor) = X.acset # synonym for getvalue

# FinDomFunctor interface
#########################

@instance ThFinDomFunctor{FinCatPres.Ob, Ob, FinCatPres.Hom, Hom,
                           FinCat, Category, FinCatPres.Gen,
                          } [model::ACSetFunctor{ACS, Ob, Hom} 
                            ] where {ACS, Ob, Hom} begin 

  dom()::FinCat = FinCat(Presentation(getvalue(model)))

  codom()::Category = Category(CollageCat(model.cod))

  function ob_map(x::GATExpr{:generator})::Ob 
    S = acset_schema(model.cod)
    x = nameof(x)
    if x ∈ ob(S)
      get_ob(model.cod, getvalue(model), x)
    else 
      TaggedElem(get_attrtype(model.cod, getvalue(model), x), x)
    end
  end 

  hom_map(f::GATExpr)::Hom = if f isa GATExpr{:generator}
    gen_map[model](f)
  elseif f isa GATExpr{:id}
    id(codom[model](), ob_map[model](only(f.args)))
  else 
    error("TODO $f")
  end

  function gen_map(f::GATExpr{:generator})::Hom 
    S = acset_schema(model.cod)
    f = nameof(f)
    if f ∈ homs(S; just_names=true)
      get_hom(model.cod, getvalue(model), f)
    else 
      TaggedElem(get_attr(model.cod, getvalue(model), f), codom(S, f))
    end

  end
end

FinDomFunctor(acs::ACSet; cat=nothing) = 
  FinDomFunctor(ACSetFunctor(acs, isnothing(cat) ? infer_acset_cat(acs) : cat)) |> validate


# Converting Diagrams to ACSets if possible
###########################################


""" Set-valued FinDomFunctors as ACSets. """
function (::Type{ACS})(F::FinDomFunctor) where ACS <: ACSet
  getvalue(F) isa ACSetFunctor && return getvalue(F).acset
  X = ACS()
  copy_parts!(X, F)
  return X
end

""" Copy parts from a set-valued `FinDomFunctor` to an `ACSet`.
"""
function ACSetInterface.copy_parts!(X::ACSet, F::FinDomFunctor)
  pres = presentation(getvalue(dom(F))) # assume FinCatPresentation
  added = Dict(Iterators.map(generators(pres, :Ob)) do c
    c = nameof(c)
    c => add_parts!(X, c, length(ob_map(F, pres[c])))
  end)
  for f in generators(pres, :Hom)
    dom_parts, codom_parts = added[nameof(dom(f))], added[nameof(codom(f))]
    set_subpart!(X, dom_parts, nameof(f), codom_parts[collect(hom_map(F, pres[f]))])
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

end #module

module ACSetCats
export ACSetCat

using StructEquality

using GATlab, ACSets
using ACSets.DenseACSets: attrtype_type, attr_type

import .....Theories: dom, codom
using .....BasicSets
using ....Cats, ....SetCats
using ...Heteromorphisms
using ...CSets, ...ACSetTransformations
import ..CSetCats: coerce_component
using ..PointwiseCats: AbsACSetCat

using .ThACSetCategory

# Trivial cat with underlying set being Right
@struct_hash_equal struct RightTrivialCat{T} end

RightTrivialCat(T::Type) = RightTrivialCat{T}()

# ThCategoryExplicitSets Implementation
#######################################

@instance ThCategoryExplicitSets{Nothing,Nothing} [model::RightTrivialCat{T}] where T  begin
  dom(::Nothing) = nothing

  codom(::Nothing) = nothing

  id(::Nothing) = nothing

  compose(::Nothing,::Nothing) = nothing

  ob_set()::SetOb = SetOb(SingletonSet())

  hom_set()::SetOb = SetOb(SingletonSet())

end

@instance ThCategoryWithMonicsEpics{Nothing,Nothing} [model::RightTrivialCat{T}] where T  begin
  is_monic(::Nothing) = true
  is_epic(::Nothing) = true
end

@instance ThConcreteCategory{Nothing,Nothing} [model::RightTrivialCat{T}] where T  begin
  ob_map(::Nothing) = SetOb(EitherSet(FinSet(EmptySet()), SetOb(T)))
  hom_map(::Nothing) = id[SetC()](either(FinSet(EmptySet()), SetOb(T)))
  lift(::AbstractFunction, ::Nothing, ::Nothing) = nothing
end

@instance ThCategoryWithInitial{Nothing,Nothing} [model::RightTrivialCat{T}] where T begin 

  colimit(::EmptyDiagram)::AbsColimit = InitialColimit{Nothing,Nothing}(nothing)

  universal(::AbsColimit, ::EmptyDiagram, ::Multicospan) = nothing
end

@instance ThCategoryUnbiasedCoproducts{Nothing,Nothing} [model::RightTrivialCat{T}] where T begin 

  colimit(d::DiscreteDiagram) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::DiscreteDiagram, ::Multicospan) = nothing

end

@instance ThCategoryWithCoequalizers{Nothing,Nothing} [model::RightTrivialCat{T}] where T begin 

  colimit(d::ParallelMorphisms) = 
    ColimitCocone(Multicospan([nothing], [nothing], [nothing]), FreeDiagram(d))
  

  universal(::AbsColimit, ::ParallelMorphisms, ::Multicospan) = nothing
end

@instance ThCategoryWithPushouts{Nothing,Nothing} [model::RightTrivialCat{T}] where T begin 

  colimit(d::Multispan) = let n = length(d); ns=fill(nothing, n);
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end

  universal(::AbsColimit, ::Multispan, ::Multicospan) = nothing
end

@instance ThCategoryWithBipartiteColimits{Nothing,Nothing
  } [model::RightTrivialCat{T}] where T begin
  function colimit(d::BipartiteFreeDiagram)
    ns = fill(nothing, nv₂(d))
    ColimitCocone(Multicospan(nothing, ns, ns), FreeDiagram(d))
  end
  function universal(lim::AbsColimit, ::BipartiteFreeDiagram, c::Multicospan)
    composite_universal(lim, c)
  end
end



# HeteroMorphisms 
#################

"""
Model of heteromorphisms where the domain and heteromorphisms are setfunctions 
but the codomain is trivial. 
"""
@struct_hash_equal struct TrivialCodom end 

@instance ThHeteroMorphism{FinSetInt, Nothing, FinFunction, Nothing, FinDomFunction
                          } [model::TrivialCodom] begin
  dom(h::FinDomFunction)::FinSetInt = getvalue(dom(h))
  codom(::FinDomFunction)::Nothing = nothing
  pre(a::FinFunction, h::FinDomFunction)::FinDomFunction = precompose(h, a)
  post(a::FinDomFunction, ::Nothing) = a
end 

@instance ThConcreteHeteroMorphism{
    FinSetInt, Nothing, FinFunction, Nothing, FinDomFunction
 } [model::TrivialCodom] begin

  function hom_map(f::FinDomFunction)
    
    ι = SetFunction(x->Right(x), codom(f), 
                    either(FinSet(EmptySet()), codom(f)))
    SetFunction(CopairedFinDomFunction(postcompose(f, ι)))
  end

  function lift(f::AbstractFunction, a::FinSetInt, ::Nothing)
    getvalue(dom(f)) == a  || error("Bad domain")
    cd = getvalue(codom(f))
    cd isa EitherSet || error("$f Expected EitherSet codom got $cd")
    getvalue(left(cd)) isa EmptySet || error("Expected Empty Left set $cd")
    # we need to undo the Right(x) postcomposition
    π = SetFunction(x -> getvalue(x), codom(f), right(cd))
    postcompose(f, π)
  end

end


# ACSetCategory
###############

"""
The category of attributed C-sets and tight homomorphisms is isomorphic to a
slice category of C-Set, as explained in our paper "Categorical Data Structures
for Technical Computing". Colimits in this category thus reduce to colimits of
C-sets, by a standard result about slice categories. Limits are more complicated
and are currently not supported.
"""
@struct_hash_equal struct ACSetCat <: AbsACSetCat
  constructor::Any
  function ACSetCat(x::ACSet)
    new(constructor(x))
  end
end

ACSetCat(T::Type) = ACSetCat(T())

@instance ThACSetCategory{
    Ob = FinSetInt, Hom = FinFunction, 
    AttrType = Nothing, Op = Nothing, Attr = FinDomFunction, 
  } [model::ACSetCat] begin

  constructor()::ACSet = model.constructor()

  # Interpreting the data from the ACSet as living in some collage category
  entity_cat() = SkelFinSet()

  attr_cat(s::Symbol) = RightTrivialCat(
    attrtype_type(constructor[model](),s))

  prof_cat(::Symbol) = TrivialCodom()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSetInt, c::FinSetInt) = 
    coerce_component(f, FinSet(d), FinSet(c))

  coerce_op(::Any,::Nothing,::Nothing) = nothing

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  get_ob(x::ACSet, o::Symbol)::FinSetInt = FinSetInt(nparts(x,  o))

  function get_hom(x::ACSet, h::Symbol)::FinFunction 
    S = acset_schema(x)
    if h ∈ ob(S)
      FinFunction(FinSet(get_ob[model](x, h)))
    else 
      FinFunction(x[h], FinSet(get_ob[model](x, codom(model,h))))
    end
  end

  get_op(::ACSet,::Symbol)::Nothing = error("No ops in schemas")

  get_attr(x::ACSet, h::Symbol)::FinDomFunction = 
    FinDomFunction(x[h], SetOb(attr_type(x, h)))
  
  get_attrtype(::ACSet,::Symbol)::Nothing = nothing

end

coerce_attr_component_nothing(::Symbol, ::Nothing) = nothing 

coerce_attr_component_nothing(o::Symbol, f::SetFunction) = 
  isempty(f) ? nothing : error("Bad $o component: $f")

coerce_attr_component_nothing(o::Symbol, f::Vector) = 
  isempty(f) ? nothing : error("Bad $o component: $f")


end # module

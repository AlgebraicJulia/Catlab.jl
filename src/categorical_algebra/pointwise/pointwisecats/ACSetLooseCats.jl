module ACSetLooseCats 

export LooseACSetCat

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
using ..ACSetCats: TrivialCodom

""" Just like `SetC` but its concrete category model is wrapped in `Right` """
@struct_hash_equal struct RightTypeSetC end 


@instance ThCategoryExplicitSets{Type, SetFunction} [model::RightTypeSetC] begin
  dom(f::SetFunction)::Type = eltype(dom(f))
  
  codom(f::SetFunction)::Type = eltype(codom(f))

  id(A::Type)::SetFunction = SetFunction(TypeSet(A))

  function compose(f::SetFunction, g::SetFunction)::SetFunction
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end

  ob_set() = SetOb(TypeSet)

  hom_set() = SetOb(SetFunction)
end


@instance ThConcreteCategory{Type, SetFunction
                                } [model::RightTypeSetC] begin

  ob_map(f::Type) = either(SetOb(EmptySet()), SetOb(f))
  hom_map(f::SetFunction) = SetFunction(WrappedFunction(f, Right))
  function lift(f::AbstractFunction, a::Type, b::Type)
    dom(f) == SetOb(a) || error("Bad dom $(dom(f)) ≠ $a")
    codom(f) == SetOb(b) || error("Bad codom $(codom(f)) ≠ $b")
    unwrap(f, Right)
  end
end


@instance ThCategoryUnbiasedProducts{Type,SetFunction} [model::RightTypeSetC] begin 

  function limit(a::DiscreteDiagram)::AbsLimit
    feet = Type[a...]
    X = SetOb(ProdSet(SetOb.(feet)))
    πs = [ SetFunction(x -> getindex(x, i), X, SetOb(Xi)) for (i, Xi) in enumerate(a)]
    LimitCone(Multispan{Type, SetFunction, Type}(eltype(X), πs, feet), FreeDiagram(a))
  end  

  function universal(res::AbsLimit, ::DiscreteDiagram, span::Multispan)
    @assert length(cone(res)) == length(span)
    fs = Tuple(legs(span))
    SetFunction(x -> map(f -> f(x), fs), SetOb(apex(span)), SetOb(ob(res)))
  end
end

""" We currently do NOT implement pullbacks in Set, but we can do it if the 
apex of the cospan is terminal."""
@instance ThCategoryWithPullbacks{Type,SetFunction} [model::RightTypeSetC] begin 
  function limit(cospan::Multicospan)::AbsLimit 
    apex(cospan) ∈ [Nothing, Tuple{}] || error(
      "Only support 'pullbacks' over the terminal, i.e. products. Got $(apex(cospan))")
    limit[model](DiscreteDiagram(feet(cospan)))
  end

  function universal(res::AbsLimit, cospan::Multicospan, x::Multispan) 
    universal(res, DiscreteDiagram(feet(cospan)), x)
  end  
end

""" 
A model of heteromorphisms where both domain and codomain are SetFunctions, 
pre/post composition is just ordinary composition.
"""
@struct_hash_equal struct SkelFinToRightSetHeteroMorphism end 

@instance ThHeteroMorphism{FinSetInt, Type, FinFunction, SetFunction, FinDomFunction
                          } [model::SkelFinToRightSetHeteroMorphism] begin 
  pre(a::FinFunction, h::FinDomFunction) = precompose(h, a)
  post(h::FinDomFunction, a::SetFunction) = postcompose(h, a)
end 

@instance ThConcreteHeteroMorphism{
    DomOb=FinSetInt, CodOb=Type, DomHom=FinFunction, 
  CodHom=SetFunction, Het=FinDomFunction
 } [model::SkelFinToRightSetHeteroMorphism]begin
  
  function hom_map(f::FinDomFunction)
    ι = SetFunction(x->Right(x), codom(f), 
                    either(FinSet(EmptySet()), codom(f)))
    SetFunction(CopairedFinDomFunction(postcompose(f, ι)))
  end

  function lift(f::AbstractFunction, a::FinSetInt, b::Type)
    getvalue(dom(f)) == a  || error("Bad domain")
    cd = getvalue(codom(f))
    cd isa EitherSet || error("$f Expected EitherSet codom got $cd")
    getvalue(left(cd)) isa EmptySet || error("Expected Empty Left set $cd")
    # we need to undo the Right(x) postcomposition
    π = SetFunction(x -> getvalue(x), codom(f), right(cd))
    postcompose(f, π)
  end
end



""" Loose transformation between attributed C-sets.

Limits and colimits in the category of attributed C-sets and loose homomorphisms
are computed pointwise on both objects *and* attribute types. This implies that
(co)limits of Julia types must be computed. Due to limitations in the
expressivity of Julia's type system, only certain simple kinds of (co)limits,
such as products, are supported.

Alternatively, colimits involving loose acset transformations can be constructed
with respect to explicitly given attribute type components for the legs of the
cocone, via the keyword argument `type_components` to `colimit` and related
functions. This uses the universal property of the colimit. To see how this
works, notice that a diagram of acsets and loose acset transformations can be
expressed as a diagram D: J → C-Set (for the C-sets) along with another diagram
A: J → C-Set (for the attribute sets) and a natural transformation α: D ⇒ A
(assigning attributes). Given a natural transformation τ: A ⇒ ΔB to a constant
functor ΔB, with components given by `type_components`, the composite
transformation α⋅τ: D ⇒ ΔB is a cocone under D, hence factors through the
colimit cocone of D. This factoring yields an assigment of attributes to the
colimit in C-Set.
"""
@struct_hash_equal struct LooseACSetCat <: AbsACSetCat
  constructor::Any
  function LooseACSetCat(x::ACSet)
    new(constructor(x))
  end
end

LooseACSetCat(T::Type) = LooseACSetCat(T())

@instance ThACSetCategory{
    Ob = FinSetInt, Hom = FinFunction, 
    AttrType = Type, Op = SetFunction, Attr = FinDomFunction, 
  } [model::LooseACSetCat] begin

  constructor()::ACSet = model.constructor()

  # Interpreting the data from the ACSet as living in some collage category
  entity_cat() = SkelFinSet()

  attr_cat(::Symbol) = RightTypeSetC()

  prof_cat(::Symbol) = SkelFinToRightSetHeteroMorphism()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSetInt, c::FinSetInt) = 
    coerce_component(f, FinSet(d), FinSet(c))

  function coerce_op(f::Any,a::Type,b::Type)::SetFunction
    if f isa AbstractFunction 
      dom(f) == SetOb(a) && codom(f) == SetOb(b) && return f
      eltype(dom(f)) == a || error("Bad dom: got $(dom(f)) expected $a")
      eltype(codom(f)) == b || error("Bad dom: got $(codom(f)) expected $b")
      SetFunction(x->f(x), SetOb(a), SetOb(b))
    elseif f isa Function 
      SetFunction(f, SetOb(a), SetOb(b))
    elseif isnothing(f)
      if a == b 
        return SetFunction(SetOb(a)) 
      elseif b in [Nothing, Tuple{}]
        val = b == Nothing ? nothing : ()
        SetFunction(ConstantFunction(val, SetOb(a), SetOb(b)))
      else 
        error(
        "No component mapping provided but need a function $a→$b")
      end
    else 
      error("Unexpected $f")
    end
  end

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

  get_op(::ACSet,::Symbol)::SetFunction = error("No ops in schemas")

  get_attr(x::ACSet, h::Symbol)::FinDomFunction = 
    FinDomFunction(x[h], SetOb(attr_type(x, h)))
  
  get_attrtype(x::ACSet,h::Symbol)::Type = attrtype_type(x, h)

end

end # module


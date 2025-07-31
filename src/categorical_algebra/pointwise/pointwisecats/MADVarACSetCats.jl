module MADVarACSetCats 
export MADVarACSetCat

using StructEquality, MLStyle
using GATlab, ACSets
using ACSets.DenseACSets: attr_type, attrtype_type

using .....BasicSets, ....SetCats
using .....Theories: compose
using ....Cats: ThCategoryExplicitSets, ThCategoryUnbiasedProducts, lift, hom_map, ConcreteCategory
using ...CSets, ...ACSetTransformations
using ...Heteromorphisms
using ..PointwiseCats: AbsACSetCat
using ..ACSetCats: TrivialCodom
using ..MADACSetCats: coerce_component

using .ThACSetCategory


""" 
HeteroMorphism composition appropriate for C ⇥ D where C isa FinSet-like 
category and D is a category with Kleisli composition.
"""
@struct_hash_equal struct VarProf{T} end 

@instance ThHeteroMorphism{DomOb=FinSet,CodOb=FinSet,DomHom=FinFunction, 
  CodHom=CopairedFinDomFunction, Het=CopairedFinDomFunction
                          } [model::VarProf{T}] where T begin

  dom(g::CopairedFinDomFunction) = dom[KleisliC(T)](g)
  
  codom(g::CopairedFinDomFunction) = codom[KleisliC(T)](g)

  pre(f::FinFunction, g::CopairedFinDomFunction) = 
    precompose(get(g), f) |> CopairedFinDomFunction

  post(f::CopairedFinDomFunction, g::CopairedFinDomFunction) = compose[KleisliC(T)](f, g)

end 

@instance ThConcreteHeteroMorphism{
    DomOb=FinSet,CodOb=FinSet,DomHom=FinFunction, 
  CodHom=CopairedFinDomFunction, Het=CopairedFinDomFunction
 } [model::VarProf{T}] where T begin

  hom_map(f::CopairedFinDomFunction) = hom_map[KleisliC(T)](f)

  lift(f::AbstractFunction, a::FinSet, b::FinSet) = 
    lift[KleisliC(T)](f,a,b)
end




"""
The category of C-Sets has objects which are dense ACSets with no attributes.
These are diagrams in the skeleton of FinSet.
"""
@struct_hash_equal struct MADVarACSetCat <: AbsACSetCat
  constructor::Any
  function MADVarACSetCat(x::ACSet{BitSetParts})
    new(constructor(x))
  end
end

MADVarACSetCat(s::Type) = MADVarACSetCat(s())

@instance ThACSetCategory{
    Ob = FinSet, Hom = FinFunction, 
    AttrType = FinSet, Op = CopairedFinDomFunction, Attr = CopairedFinDomFunction,
  } [model::MADVarACSetCat] begin
 
  # Interpreting the data from the ACSet as living in some collage category

  entity_cat() = FinSetC()

  attr_cat(T::Symbol) = KleisliC(attrtype_type(model, T)) 

  prof_cat(T::Symbol) = VarProf{attrtype_type(model, T)}()

  # An empty ACSet (useful for implementation details e.g. indexing)

  constructor()::ACSet = model.constructor()

  # Interpret user-friendly ACSetTransformation data in an intuitive way

  coerce_hom(f::Any, d::FinSet, c::FinSet) = coerce_component(f,d,c)

  function coerce_op(f::Any,d::FinSet,c::FinSet; context)::CopairedFinDomFunction
    𝒫 = prof_cat[model](context[:t])
    T = attrtype_type(constructor[model](), context[:t])

    f isa CopairedFinDomFunction && return lift[𝒫](SetFunction(f),d,c)
    f isa AbstractFunction && return lift[𝒫](f, d, c) 
    coerce_attr_varfun(f, T, FinSet(d), FinSet(c))
  end

  # Extracting Ob/Hom data from an ACSet data structure

  get_ob(x::ACSet, o::Symbol)::FinSet = FinSet(Set(parts(x, o)))

  function get_hom(x::ACSet, h::Symbol)::FinFunction
    S = acset_schema(x)
    if h ∈ ob(S)
      SetFunction(get_ob[model](x, h))
    else
      v = Dict{Int,Int}([p=>x[p,h] for p in parts(x, dom(S, h))])
      FinFunction(v, get_ob[model](x, codom(S, h)))
    end
  end

  get_op(::ACSet, ::Symbol)::Union{} = error("No ops in schemas")

  function get_attr(x::ACSet, h::Symbol)::CopairedFinDomFunction
    S, T = acset_schema(x), attr_type(x, h)
    v = map(parts(x, dom(S, h))) do p
      elem = x[p,h]
      p => elem isa AttrVar ? Left(getvalue(elem)) : Right{T}(elem)
    end
    cod = either(FinSet(Set(parts(x, codom(S,h)))), SetOb(attr_type(x, h)))
    FinDomFunction(Dict{Int,Union{Left{Int},Right{T}}}(v), cod) |> CopairedFinDomFunction
  end

  get_attrtype(x::ACSet, o::Symbol)::FinSet = FinSet(Set(parts(x, o)))

end


function coerce_attr_varfun(::Nothing, T::Type, d::FinSet, cd::FinSet) 
  isempty(d) || error("Bad: nonempty domain $d")
  return FinDomFunction(Dict{eltype(d), eltype(cd)}(), either(cd,SetOb(T))) |> CopairedFinDomFunction
end

"""  """
function coerce_attr_varfun(f::FinDomFunction, T::Type, d::FinSet, cd::FinSet)
  sort(collect(dom(f))) == sort(collect(d)) || error("Bad: mismatched dom $d ≠ $(dom(f))")
  # first we optimistically assume that we already have a VarFunction
  codom(f) == either(SetOb(cd), SetOb(T)) && return f
  codom(f) == either(cd, SetOb(T)) && return f
  # otherwise Assume this is a function purely on the FinSet component
  codom(f) == cd || error("Bad: mismatched codom: \n\tExpected $(either(SetOb(cd), SetOb(T))) or $cd\n\tGOT      $(codom(f))")
  pure(f, T) |> CopairedFinDomFunction
end

""" 
Abstract vector may have junk data in areas where domain is not defined 
"""
function coerce_attr_varfun(f::AbstractVector, T::Type, d::FinSet, cd::FinSet) 
  def_domain = findall(v->v!=AttrVar(0), f)
  getvalue(d) isa FinSetHash || error("Domain set wrong impl $(getvalue(d))")
  Set(def_domain) == Set(collect(d))  ||  error("Bad domain $def_domain ($d) for $f")
  d = map(def_domain) do k
    v = f[k]
    k => if v isa AttrVar
      getvalue(v) ∈ cd || error("Bad value $v for codom $cd")
      Left(getvalue(v))
    elseif v isa T
      Right(v)
    else
      error("Bad::$T value: $v :: $(typeof(v))")
    end
  end
  FinDomFunction(Dict(d), FinSet(Set(def_domain)), either(cd, SetOb(T))
   ) |> CopairedFinDomFunction
end

end # module

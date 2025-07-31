module Heteromorphisms 

export ThHeteroMorphism, SetHeteroMorphism, Hetero, 
       VarFunctionHeteroMorphism, post, pre, CoproductHeteroMorphism,
       ThConcreteHeteroMorphism, ConcreteHeteroMorphism

using StructEquality, MLStyle
using GATlab

import .....Theories: dom, codom
using .....BasicSets
using ....SetCats
using ....Cats
import ....Cats: lift, hom_map

"""A naive theory of heteromorphisms which involves three types: 
domain morphisms, codomain morphisms, and heteromorphisms, which can be 
pre/postcomposed.
"""
@theory ThHeteroMorphism begin
  DomOb::TYPE; CodOb::TYPE; 
  DomHom(dom::DomOb, codom::DomOb)::TYPE; 
  CodHom(dom::CodOb,codom::CodOb)::TYPE;
  Het(dom::DomOb,codom::CodOb)::TYPE
  pre(a::DomHom(x,y), h::Het(y,z))::Het(x,z) ⊣ [(x,y)::DomOb, z::CodOb]
  post(h::Het(x,y), b::CodHom(y,z))::Het(x,z) ⊣ [x::DomOb, (y,z)::CodOb]
end

ThHeteroMorphism.Meta.@wrapper Hetero

""" See ThConcreteCategory """
@theory ThConcreteHeteroMorphism <: ThHeteroMorphism begin
  FFun::TYPE{AbstractFunction}
  hom_map(h::Het(a::DomOb,b::CodOb))::FFun
  lift(f::FFun, a::DomOb, b::CodOb)::Het(a,b)
  
  lift(hom_map(h), a, b) == h ⊣ [a::DomOb, b::CodOb, h::Het(a,b)]
end

ThConcreteHeteroMorphism.Meta.@wrapper ConcreteHeteroMorphism

# Example models of ThHeteroMorphism
####################################

""" 
A model of heteromorphisms where both domain and codomain are SetFunctions, 
pre/post composition is just ordinary composition 
"""
@struct_hash_equal struct SetHeteroMorphism end 

@instance ThHeteroMorphism{SetOb, SetOb, SetFunction, SetFunction, SetFunction
                          } [model::SetHeteroMorphism] begin 
  pre(a::SetFunction, h::SetFunction) = compose[SetC()](a, h)
  post(a::SetFunction, h::SetFunction) = compose[SetC()](a, h)
end 

"""
Heteromorphism from 𝒞 → 𝒟 where 𝒟 is a coproduct indexed by keys. In this case, 
the Heteromorphisms must also be indexed. We assume they all share a common
domain category 𝒞.
"""
@struct_hash_equal struct CoproductHeteroMorphism{DO,CO,DH,CH,Het}
  val::Dict{<:Any, Hetero}
  function CoproductHeteroMorphism(vals::Dict{<:Any, Hetero}, domcat::Category)
    DO, DH = impl_type.(Ref(domcat),[:Ob,:Hom])

    if isempty(vals) 
      return new{DO,Union{},DH,Union{},Union{}}(Dict{Any,Hetero}())
    end

    SumCO, SumCH, SumHet = map([:CodOb, :CodHom, :Het]) do x 
      Tagged(Dict{Any, Type}(k=>impl_type(v, x) for (k,v) in vals))
    end

    DOs, DHs = map([:DomOb, :DomHom]) do x 
      unique(impl_type.(collect(values(vals)), x)) 
    end

    length(DOs) == 1 || error("Nonunique domain obs for CoproductHeteroMorphism")
    DO == only(DOs) || error("Bad domcat homtype $O ≠ $(only(DOs))")

    length(DHs) == 1 || error("Nonunique domain homs for CoproductHeteroMorphism")
    DH == only(DHs) || error("Bad domcat homtype $H ≠ $(only(DHs))")

    new{DO, SumCO, DH, SumCH, SumHet}(vals)
  end
end

GATlab.getvalue(c::CoproductHeteroMorphism) = c.val

Base.getindex(c::CoproductHeteroMorphism, i) = c.val[i]

@instance ThHeteroMorphism{DO,CO,D,C,H} [model::CoproductHeteroMorphism{DO,CO,D,C,H}
                                        ] where {DO,CO,D,C,H} begin
  dom(h::H) = dom(model[gettag(h)], getvalue(h))
  codom(h::H) = TaggedElem(codom(model[gettag(h)], getvalue(h)), gettag(h))
  pre(a::D, h::H) = TaggedElem(pre(model[gettag(h)], a, getvalue(h)), gettag(h))
  post(a::H, h::C) = TaggedElem(post(model[gettag(h)], a, getvalue(h)), gettag(h))
end 

end # module 

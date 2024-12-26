module Heteromorphisms 

export ThHeteroMorphism, SetHeteroMorphism, TrivialCodom, Hetero, 
       VarFunctionHeteroMorphism

using StructEquality, MLStyle
using GATlab

using .....BasicSets
using ....SetCats
using ....Cats

"""A naive theory of heteromorphisms which involves three types: 
domain morphisms, codomain morphisms, and heteromorphisms, which can be 
pre/postcomposed.
"""
@theory ThHeteroMorphism begin 
  Dom::TYPE; Cod::TYPE; Het::TYPE
  pre(a::Dom, h::Het)::Het
  post(h::Het, b::Cod)::Het
end

ThHeteroMorphism.Meta.@wrapper Hetero

# Example models of ThHeteroMorphism
####################################

""" 
A model of heteromorphisms where both domain and codomain are SetFunctions, 
pre/post composition is just ordinary composition 
"""
@struct_hash_equal struct SetHeteroMorphism end 

@instance ThHeteroMorphism{SetFunction, SetFunction, SetFunction
                          } [model::SetHeteroMorphism] begin 
  pre(a::SetFunction, h::SetFunction) = compose[SetC()](a, h)
  post(a::SetFunction, h::SetFunction) = compose[SetC()](a, h)
end 

"""
Model of heteromorphisms where the domain and heteromorphisms are setfunctions 
but the codomain is discrete (only identity morphisms)
"""
@struct_hash_equal struct TrivialCodom end 

@instance ThHeteroMorphism{SetFunction, Nothing, SetFunction
                          } [model::TrivialCodom] begin 
  pre(a::SetFunction, h::SetFunction) = compose[SetC()](a, h)
  post(a::SetFunction, ::Nothing) = a
end 

""" 
"""
@struct_hash_equal struct VarFunctionHeteroMorphism end 

@instance ThHeteroMorphism{FinFunction, FinFunction, VarFunction
                          } [model::VarFunctionHeteroMorphism] begin 
  pre(a::FinFunction, h::VarFunction) = compose[AttrC{get_type(h)}()](a, h)

  post(a::VarFunction, h::FinFunction) = compose[AttrC{get_type(a)}()](a, h)
end 

end # module 

module FDFsAsSetFuns

export FinDomFunctionAsSetFunction

using StructEquality

using GATlab

using ..BasicSets: SetFunction′, SetOb, ThSetFunction, FinFunction, FinDomFunction
import ..BasicSets: SetFunction
using .ThSetFunction

@struct_hash_equal struct FinDomFunctionAsSetFunction{C,D}
  val::FinDomFunction
  FinDomFunctionAsSetFunction(f::FinDomFunction) = 
    new{impl_type.(Ref(f), [:Dom,:Cod])...}(f)
end 

GATlab.getvalue(f::FinDomFunctionAsSetFunction) = f.val

SetFunction(f::FinDomFunction) =  SetFunction(FinDomFunctionAsSetFunction(f))
SetFunction(f::FinFunction) =  SetFunction(FinDomFunction(f))

@instance ThSetFunction{A,B} [model::FinDomFunctionAsSetFunction{A,B}] where {A,B} begin 
  dom()::SetOb = SetOb(dom(getvalue(model)))

  codom()::SetOb = codom(getvalue(model))

  app(i::A)::B = app(getvalue(model), i)

  postcompose(f::SetFunction′)::SetFunction′ =  SetFunction(getvalue(model), f)

end

end # module

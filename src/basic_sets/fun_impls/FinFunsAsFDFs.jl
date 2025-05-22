module FinFunsAsFDFs 

export FinFunAsFinDomFunction

using StructEquality

using GATlab

using ..BasicSets: FinFunction, SetFunction, FinSet, SetOb, FinDomFunction′, ThFinDomFunction
import ..FinDomFunctions: FinDomFunction
using .ThFinDomFunction

@struct_hash_equal struct FinFunAsFinDomFunction{C,D,I}
  val::WithModel{I}
  function FinFunAsFinDomFunction(f::FinFunction) 
    m = getvalue(f)
    new{impl_type.(Ref(f), [:Dom,:Cod])..., typeof(m)}(WithModel(m))
  end
end 

GATlab.getvalue(f::FinFunAsFinDomFunction) = f.val

FinDomFunction(f::FinFunction) =  FinDomFunction(FinFunAsFinDomFunction(f))
FinDomFunction(f::FinSet) = FinDomFunction(FinFunction(f)) # identity FinDomFunction

@instance ThFinDomFunction{A,B} [model::FinFunAsFinDomFunction{A,B}] where {A,B} begin 
  dom()::FinSet = dom(getvalue(model))

  codom()::SetOb = SetOb(codom(getvalue(model)))

  app(i::A)::B = app(getvalue(model), i)

  # precompose(f::FinFunction)::FinDomFunction = FinDomFunction(f, getvalue(model))

  postcompose(f::SetFunction)::FinDomFunction =  FinDomFunction(getvalue(model), f)

end

end # module
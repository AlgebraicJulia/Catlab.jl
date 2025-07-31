module WrappedFunctions 

export WrappedFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage 

using ..BasicSets

using .ThSetFunction


"""
A wrapper `W` is a type which wraps values of type `T` (yielding a value of type 
`W{T}`). Applying this to a function turns its domain and codomain into wrapped
domains and codomains.
"""
@struct_hash_equal struct WrappedFunction{F,D<:AbsSet,C<:AbsSet,DT,CT}
  fun::WithModel{F}
  d::D
  c::C
  function WrappedFunction(f::AbstractFunction, W::Type)
    dc = dom(f), codom(f)
    td,tc = eltype.(dc)
    f′ = getvalue(f)
    w = WithModel(f′)
    new{typeof(f′), typeof.(dc)..., W{td}, W{tc}}(w, dc...)
  end
end

Base.get(w::WrappedFunction) = w.fun

@instance ThFinFunction{DT,CT} [
    model::WrappedFunction{F,FinSet,FinSet,DT,CT}] where {F,DT,CT} begin

  dom()::FinSet = WrappedSet(model.d, W)

  codom()::FinSet = WrappedSet(model.c, W)

  function app(i::DT)::CT
    W(app(get(model), getvalue(i)))
  end

  postcompose(f::FinFunction′)::FinFunction′ = FinFunction(model, f)

end


@instance ThFinDomFunction{DT,CT} [
    model::WrappedFunction{F,FinSet,SetOb,DT,CT}] where {F,DT,CT} begin

  dom()::FinSet = WrappedSet(model.d, W)

  codom()::SetOb = WrappedSet(model.c, W)

  function app(i::DT)::CT
    W(app(get(model), getvalue(i)))
  end

  postcompose(f::SetFunction′)::FinFunction′ = FinDomFunction(model, f)

end


@instance ThSetFunction{DT,CT} [
    model::WrappedFunction{F,SetOb,SetOb,DT,CT}] where {F,DT,CT} begin

  dom()::SetOb = WrappedSet(model.d, W)

  codom()::SetOb = WrappedSet(model.c, W)

  function app(i::DT)::CT
    W(app(get(model), getvalue(i)))
  end

  postcompose(f::SetFunction′)::SetFunction′ = SetFunction(model, f)

end

end # module

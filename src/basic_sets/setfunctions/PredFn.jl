module PredFn 
export PredicatedFunction

using ....Theories: dom, codom
using ..Sets, ..SetFunctions

const PredicatedFunction{T,T′} =
  SetFunctionCallable{T,T′,PredicatedSet{T},PredicatedSet{T′}}

function (f::PredicatedFunction{T,T′})(x::T)::T′ where {T,T′}
  dom(f)(x) || error("Predicate not satisfied on input: $x")
  y = f.func(x)
  codom(f)(y) || error("Predicate not satisfied on output: $y")
  y
end

end #module

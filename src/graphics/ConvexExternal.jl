# External packages.
using .Convex, .SCS

using Compat
import .WiringDiagramLayouts: solve_isotonic

function solve_isotonic(y::Vector, ::Val{:convexjl};
                        solver=SCSSolver(verbose=0), loss=sumsquares,
                        lower::Number=-Inf, upper::Number=Inf, pad::Number=0)
  if isempty(y)
    return empty(y)
  end
  x = Variable(length(y))
  constraints = Constraint[ x[i] - x[i-1] >= pad for i in 2:length(x) ]
  if lower != -Inf
    push!(constraints, x[1] >= lower)
  end
  if upper != Inf
    push!(constraints, x[end] <= upper)
  end
  solve!(minimize(loss(x-y), constraints), solver)
  length(x) == 1 ? [ x.value ] : dropdims(x.value, dims=2) # XXX: MATLAB-ism.
end

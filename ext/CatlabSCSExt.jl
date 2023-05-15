module CatlabSCSExt

using SCS

import Catlab.Graphics.WiringDiagramLayouts: has_port_layout_method, solve_isotonic

has_port_layout_method(::Type{Val{:isotonic}}) = true

function solve_isotonic(y::Vector; solver=SCS.Optimizer,
                        loss=sumsquares, lower::Number=-Inf, upper::Number=Inf,
                        pad::Number=0)
  # HACK: sort of a hacky way around the lack of multiple package dependencies for an extension
  # Hopefully this is a feature that can be added and this hack can be removed
  try
    using Convex
  catch e
    error("Convex is required along with SCS for isotonic regression.")
  end
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
  solve!(minimize(loss(x-y), constraints), solver;
         verbose=false, silent_solver=true)
  length(x) == 1 ? [ x.value ] : dropdims(x.value, dims=2) # XXX: MATLAB-ism.
end

end

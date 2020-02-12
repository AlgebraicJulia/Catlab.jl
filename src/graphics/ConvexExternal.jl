# External packages.
using .Convex, .SCS

using Compat
using Statistics: mean

using ..WiringDiagrams, .WiringDiagramLayouts
using .WiringDiagramLayouts: WireLayout, LayoutOptions, layout_linear_ports,
  position, svector
import .WiringDiagramLayouts: layout_outer_ports


function layout_outer_ports(diagram::WiringDiagram, opts::LayoutOptions,
                            ::Val{:isotonic})
  inputs, outputs = input_ports(diagram), output_ports(diagram)
  diagram_size = diagram.value.size
  port_dir = svector(opts, 0, 1)
  port_coord = v -> dot(v, port_dir)
  max_range = port_coord(diagram_size)
  pad = opts.base_box_size + opts.parallel_pad
  solver = SCSSolver(verbose=0)
  
  # Solve optimization problem for input ports.
  # Note that we are minimizing distance only along the port axis, not in the
  # full Euclidean plan.
  ys = [ Float64[] for i in eachindex(inputs) ]
  for wire in out_wires(diagram, input_id(diagram))
    i, layout = wire.source.port, wire.value::WireLayout
    if !(isnothing(layout) || isempty(layout))
      push!(ys[i], port_coord(position(first(layout))))
    elseif wire.target.box != output_id(diagram)
      push!(ys[i], port_coord(position(diagram, wire.target)))
    end
  end
  y = Float64[ isempty(y) ? 0.0 : mean(y) for y in ys ]
  in_coords = solve_isotonic!(y, solver; max_range=max_range, pad=pad)
  
  # Solve optimization problem for output ports.
  ys = [ Float64[] for i in eachindex(outputs) ]
  for wire in in_wires(diagram, output_id(diagram))
    i, layout = wire.target.port, wire.value::WireLayout
    if !(isnothing(layout) || isempty(layout))
      push!(ys[i], port_coord(position(last(layout))))
    elseif wire.source.box != input_id(diagram)
      push!(ys[i], port_coord(position(diagram, wire.source)))
    end
  end
  y = Float64[ isempty(y) ? 0.0 : mean(y) for y in ys ]
  out_coords = solve_isotonic!(y, solver; max_range=max_range, pad=pad)
  
  (layout_linear_ports(InputPort, inputs, in_coords, diagram_size, opts),
   layout_linear_ports(OutputPort, outputs, out_coords, diagram_size, opts))
end

function solve_isotonic!(y::Vector, solver; loss=sumsquares,
                         max_range::Number=Inf, pad::Number=0)
  if isempty(y); return empty(y) end
  x = Variable(length(y))
  constraints = [ [x[1] >= -max_range/2, x[end] <= max_range/2];
                  [ x[i] - x[i-1] >= pad for i in 2:length(x) ] ]
  solve!(minimize(loss(x-y), constraints), solver)
  length(x) == 1 ? [ x.value ] : dropdims(x.value, dims=2) # XXX: MATLAB-ism.
end

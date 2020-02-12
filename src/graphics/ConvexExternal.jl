# External packages.
using .Convex, .SCS

using ..WiringDiagrams, .WiringDiagramLayouts
using .WiringDiagramLayouts: LayoutOptions, layout_linear_ports, position,
  svector
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
  x, terms = Variable(length(inputs)), AbstractExpr[]
  for i in eachindex(inputs)
    tgts = [ wire.target for wire in out_wires(diagram, input_id(diagram), i)
             if wire.target.box != output_id(diagram) ]
    for tgt in unique!(tgts)
      push!(terms, x[i] - port_coord(position(diagram, tgt)))
    end
    if isempty(tgts); push!(terms, x[i]) end
  end
  in_coords = solve_isotonic!(x, terms, solver; max_range=max_range, pad=pad)
  
  # Solve optimization problem for output ports.
  x, terms = Variable(length(outputs)), AbstractExpr[]
  for i in eachindex(outputs)
    srcs = [ wire.source for wire in in_wires(diagram, output_id(diagram), i)
             if wire.source.box != input_id(diagram) ]
    for src in unique!(srcs)
      push!(terms, x[i] - port_coord(position(diagram, src)))
    end
    if isempty(srcs); push!(terms, x[i]) end
  end
  out_coords = solve_isotonic!(x, terms, solver; max_range=max_range, pad=pad)
  
  (layout_linear_ports(InputPort, inputs, in_coords, diagram_size, opts),
   layout_linear_ports(OutputPort, outputs, out_coords, diagram_size, opts))
end

function solve_isotonic!(x::Variable, terms::Vector, solver;
                         loss=sumsquares, max_range::Number=Inf, pad::Number=0)
  if isempty(x); return [] end
  objective = isempty(terms) ? 0 :
    loss(length(terms) > 1 ? hcat(terms...) : first(terms)) # XXX: Ugly.
  constraints = [ [x[1] >= -max_range/2, x[end] <= max_range/2];
                  [ x[i] - x[i-1] >= pad for i in 2:length(x) ] ]
  solve!(minimize(objective, constraints), solver)
  length(x) == 1 ? [ x.value ] : dropdims(x.value, dims=2) # XXX: MATLAB-ism.
end

""" Tensor networks from the perspective of undirected wiring diagrams.
"""
module TensorNetworks
export RelationDiagram, @tensor_network, @eval_tensor_network,
  parse_tensor_network, compile_tensor_expr

using Compat
using MLStyle: @match

using ...CategoricalAlgebra.CSets
using ...WiringDiagrams.UndirectedWiringDiagrams
import ...WiringDiagrams: oapply
using ...Programs.RelationalPrograms: RelationDiagram

# Evaluation
############

""" Contract tensors according to UWD.
"""
function oapply(d::UndirectedWiringDiagram,
                tensors::AbstractVector{<:AbstractArray})
  @assert nboxes(d) == length(tensors)
  contract_tensor_network(tensors,
                          [junction(d, ports(d, b)) for b in boxes(d)],
                          junction(d, ports(d, outer=true), outer=true))
end

""" Generalized contraction of two tensors of arbitrary rank.

This function includes matrix multiplication, tensor product, and trace as
special cases. The interface similar to that of the `ncon` ("Network
CONtractor") function in:

- the [NCON package](https://arxiv.org/abs/1402.0939) for MATLAB
- the Julia package [TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl)

except that the outer junctions are represented explictly by a third argument
rather than implicitly by using negative numbers in the second argument.
"""
function contract_tensor_network((A, B), (jA, jB), j_out)
  njunc = maximum(Iterators.flatten((jA, jB, j_out)))
  jA, jB, j_out = Tuple(jA), Tuple(jB), Tuple(j_out)
  jsizes = fill(-1, njunc)
  for (i,j) in enumerate(jA); jsizes[j] = size(A, i) end
  for (i,j) in enumerate(jB); jsizes[j] = size(B, i) end
  jsizes = Tuple(jsizes)

  C = zeros(eltype(A), Tuple(jsizes[j] for j in j_out))
  for index in CartesianIndices(jsizes)
    C[(index[j] for j in j_out)...] +=
      A[(index[j] for j in jA)...] * B[(index[j] for j in jB)...]
  end
  return C
end

# Parsing and code generation
#############################

""" Construct an undirected wiring diagram using tensor notation.

The tensor syntax is compatible with that used by packages like
[TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl) and
[TensorCast.jl](https://github.com/mcabbott/TensorCast.jl). For example, the
wiring diagram for composite of two matrices (or two binary relations) is
constructed by

```julia
@tensor_network (i,j,k) C[i,k] := A[i,j] * B[j,k]
```

The leading context, or list of variables, may be omitted, in which case it is
inferred from the variables used in the tensor expression. So, in this example,
an equivalent macro call is

```julia
@tensor_network C[i,k] := A[i,j] * B[j,k]
```

See also: [`@eval_tensor_network`](@ref), the "inverse" to this macro.
"""
macro tensor_network(exprs...)
  :(parse_tensor_network($((QuoteNode(expr) for expr in exprs)...)))
end

""" Parse an undirected wiring diagram from a tensor expression.

For more information, see the corresponding macro [`@tensor_network`](@ref).
"""
function parse_tensor_network(context::Expr, expr::Expr)
  all_vars = @match context begin
    Expr(:tuple, args...) => collect(Symbol, args)
    Expr(:vect, args...) => collect(Symbol, args)
  end
  parse_tensor_network(expr, all_vars=all_vars)
end

function parse_tensor_network(expr::Expr; all_vars=nothing)
  # Parse tensor expression.
  (outer_name, outer_vars), body = @match expr begin
    Expr(:(=), outer, body) => (parse_tensor_term(outer), body)
    Expr(:(:=), outer, body) => (parse_tensor_term(outer), body)
    _ => error("Tensor expression $expr must be an assignment, either = or :=")
  end
  names_and_vars = map(parse_tensor_term, @match body begin
    Expr(:call, :(*), args...) => args
    1 => [] # No terms
    arg => [arg] # One term
  end)

  # Check compatibility of used variables with declared variables.
  used_vars = unique!(reduce(vcat, ([[outer_vars]; last.(names_and_vars)])))
  if isnothing(all_vars)
    all_vars = sort!(used_vars)
  else
    used_vars ⊆ all_vars || error("One of variables $used_vars is not declared")
  end

  # Construct the undirected wiring diagram.
  d = RelationDiagram{Symbol}(length(outer_vars))
  add_junctions!(d, length(all_vars), variable=all_vars)
  set_junction!(d, ports(d, outer=true),
                incident(d, outer_vars, :variable), outer=true)
  for (name, vars) in names_and_vars
    box = add_box!(d, length(vars), name=name)
    set_junction!(d, ports(d, box), incident(d, vars, :variable))
  end
  return d
end

function parse_tensor_term(expr)
  @match expr begin
    Expr(:ref, name::Symbol, args...) => (name, collect(Symbol, args))
    name::Symbol => (name, Symbol[]) # Scalar
    _ => error("Invalid syntax in term $expr in tensor expression")
  end
end

""" Evaluate a tensor network using another macro.

This macro takes two arguments: an undirected wiring diagram and a macro call
supporting the tensor contraction notation that is de facto standard among Julia
tensor packages. For example, to evaluate a tensor network using the `@tullio`
macro, use:

```julia
A = @eval_tensor_network diagram @tullio
```

The following macros should work:

- `@tensor` from
  [TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl).
- `@tullio` from [Tullio.jl](https://github.com/mcabbott/Tullio.jl)
- `@einsum` from [Einsum.jl](https://github.com/ahwillia/Einsum.jl)
- `@ein` from [OMEinsum.jl](https://github.com/under-Peter/OMEinsum.jl)

However, the macros `@cast` and `@reduce` from
[TensorCast.jl](https://github.com/mcabbott/TensorCast.jl) will *not* work
because they do not support implicit summation.

See also: [`@tensor_network`](@ref), the "inverse" to this macro.
"""
macro eval_tensor_network(diagram, tensor_macro)
  # XXX: We cannot use `GeneralizedGenerated.mk_function` here because packages
  # like Tullio generate code with type parameters, which GG does not allow.
  compile_expr = :(compile_tensor_expr($(esc(diagram)),
    assign_op=:(:=), assign_name=gensym("out")))
  Expr(:call, esc(:eval),
       :(_eval_tensor_network($compile_expr, $(QuoteNode(tensor_macro)))))
end
function _eval_tensor_network(tensor_expr, macro_expr)
  @match macro_expr begin
    Expr(:macrocall, args...) => Expr(:macrocall, args..., tensor_expr)
    _ => error("Expression $macro_expr is not a macro call")
  end
end

""" Generate tensor expression from undirected wiring diagram.

This function is used to implement [`@eval_tensor_network`](@ref) but may be
useful in its own right.
"""
function compile_tensor_expr(d::UndirectedWiringDiagram;
    assign_op::Symbol=:(=), assign_name::Symbol=:out)
  vars = j -> subpart(d, j, :variable)
  outer_vars = vars(junction(d, ports(d, outer=true), outer=true))
  terms = map(boxes(d)) do box
    ref_expr(subpart(d, box, :name), vars(junction(d, ports(d, box))))
  end
  lhs = ref_expr(assign_name, outer_vars)
  rhs = if isempty(terms); 1
    elseif length(terms) == 1; first(terms)
    else Expr(:call, :(*), terms...) end
  Expr(assign_op, lhs, rhs)
end

function ref_expr(name::Symbol, vars)
  isempty(vars) ? name : Expr(:ref, name, vars...)
end

end

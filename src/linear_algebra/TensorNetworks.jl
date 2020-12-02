""" Tensor networks via the operad of undirected wiring diagrams.
"""
module TensorNetworks
export RelationDiagram, @tensor_network, parse_tensor_network,
  contract_tensor_network, @contract_tensors_with, gen_tensor_notation

using Compat
using MLStyle: @match

using ...CategoricalAlgebra.CSets
using ...WiringDiagrams.UndirectedWiringDiagrams
import ...WiringDiagrams: oapply
using ...Programs.RelationalPrograms: RelationDiagram

# Evaluation
############

""" Contract tensors according to UWD.

This method simply wraps [`contract_tensor_network`](@ref), which also presents
an interface closer to the standard tensor algebra packages.
"""
oapply(d::UndirectedWiringDiagram, tensors::AbstractVector{<:AbstractArray}) =
  contract_tensor_network(d, tensors)

""" Contract a tensor network all at once.

Performs a generalized contraction of a list of tensors of arbitrary rank. In
the binary case, this function includes matrix multiplication, tensor product,
and trace as special cases. In general, it implements the "generalized matrix
multiplication" described in [Spivak et al's "Pixel
Arrays"](https://arxiv.org/abs/1609.00061).

Be warned that this method is inefficient for contracting networks with more
than two junctions. Specifically, if the network has ``n`` junctions with
dimensions ``k₁, …, kₙ``, then this function performs exactly ``k₁ ⋯ kₙ``
multiplications in the base ring (or rig). For example, a binary matrix multiply
of square matrices performs ``k³`` multiplications. A ternary matrix multiply
performs ``k⁴`` multiplications, whereas a sequence of two binary multiplies
performs ``2k³``. Thus, when there are more than two junctions, it is usually
better to schedule a computation using [`schedule`](@ref) or another package,
possibly via [`@contract_tensors_with`](@ref).

In addition to the method taking an undirected wiring diagram, this function has
methods similar to the `ncon` ("Network CONtractor") function in:

- the [NCON package](https://arxiv.org/abs/1402.0939) for MATLAB
- the Julia package [TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl)

except that here the outer junctions are represented explictly by a third
argument rather than implicitly by using negative numbers in the second
argument.
"""
function contract_tensor_network(d::UndirectedWiringDiagram,
                                 tensors::AbstractVector{<:AbstractArray})
  @assert nboxes(d) == length(tensors)
  juncs = [junction(d, ports(d, b)) for b in boxes(d)]
  j_out = junction(d, ports(d, outer=true), outer=true)
  contract_tensor_network(tensors, juncs, j_out)
end

function contract_tensor_network(tensors::AbstractVector{<:AbstractArray{T}},
                                 juncs::AbstractVector, j_out) where T
  # Handle important binary case with specialized code.
  if length(tensors) == 2 && length(juncs) == 2
    return contract_tensor_network(Tuple(tensors), Tuple(juncs), j_out)
  end

  jsizes = Tuple(infer_junction_sizes(tensors, juncs, j_out))
  juncs, j_out = map(Tuple, juncs), Tuple(j_out)
  C = zeros(T, Tuple(jsizes[j] for j in j_out))
  for index in CartesianIndices(jsizes)
    x = one(T)
    for (A, junc) in zip(tensors, juncs)
      x *= A[(index[j] for j in junc)...]
    end
    C[(index[j] for j in j_out)...] += x
  end
  return C
end

function contract_tensor_network( # Binary case.
    (A, B)::Tuple{<:AbstractArray{T},<:AbstractArray{T}},
    (jA, jB), j_out) where T
  jsizes = Tuple(infer_junction_sizes((A, B), (jA, jB), j_out))
  jA, jB, j_out = Tuple(jA), Tuple(jB), Tuple(j_out)
  C = zeros(T, Tuple(jsizes[j] for j in j_out))
  for index in CartesianIndices(jsizes)
    C[(index[j] for j in j_out)...] +=
      A[(index[j] for j in jA)...] * B[(index[j] for j in jB)...]
  end
  return C
end

function infer_junction_sizes(tensors, juncs, j_out)
  @assert length(tensors) == length(juncs)
  njunc = maximum(Iterators.flatten((Iterators.flatten(juncs), j_out)))
  jsizes = fill(-1, njunc)
  for (A, junc) in zip(tensors, juncs)
    for (i, j) in enumerate(junc)
      if jsizes[j] == -1
        jsizes[j] = size(A, i)
      else
        @assert jsizes[j] == size(A, i)
      end
    end
  end
  @assert all(s >= 0 for s in jsizes)
  jsizes
end

# Parsing and code generation
#############################

""" Construct an undirected wiring diagram using tensor notation.

The syntax is compatible with the Einstein-style tensor notation used by tensor
algebra packages like
[TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl) and
[TensorCast.jl](https://github.com/mcabbott/TensorCast.jl). For example, the
wiring diagram for the composite of two matrices (or two binary relations) is
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

See also: [`gen_tensor_notation`](@ref), the "inverse" to this macro.
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

""" Contract a tensor network using a macro from another package.

This macro takes two arguments: an undirected wiring diagram and a macro call
supporting the tensor contraction notation that is de facto standard among Julia
tensor packages. For example, to evaluate a tensor network using the `@tullio`
macro, use:

```julia
A = @contract_tensors_with @tullio diagram
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
"""
macro contract_tensors_with(diagram, macro_expr)
  # XXX: We cannot use `GeneralizedGenerated.mk_function` here because packages
  # like Tullio generate code with type parameters, which GG does not allow.
  compile_expr = :(gen_tensor_notation($(esc(diagram)),
    assign_op=:(:=), assign_name=gensym("out")))
  Expr(:call, esc(:eval),
       :(_contract_tensors_with($compile_expr, $(QuoteNode(macro_expr)))))
end
function _contract_tensors_with(tensor_expr, macro_expr)
  @match macro_expr begin
    Expr(:macrocall, args...) => Expr(:macrocall, args..., tensor_expr)
    _ => error("Expression $macro_expr is not a macro call")
  end
end

""" Generate Julia expression in tensor notation from undirected wiring diagram.

This function is used to implement [`@contract_tensors_with`](@ref) but may be
useful in its own right.

See also [`@tensor_network`](@ref), the "inverse" to this function.
"""
function gen_tensor_notation(d::UndirectedWiringDiagram;
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

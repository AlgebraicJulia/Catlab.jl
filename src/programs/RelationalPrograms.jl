""" Parse relation expressions in Julia syntax into undirected wiring diagrams.
"""
module RelationalPrograms
export RelationDiagram, UntypedRelationDiagram, TypedRelationDiagram,
  @relation, @tensor_network, @eval_tensor_network,
  parse_relation_diagram, parse_tensor_network, compile_tensor_expr

using Compat
using MLStyle: @match

using ...CategoricalAlgebra.CSets, ...Present
using ...WiringDiagrams.UndirectedWiringDiagrams
using ...WiringDiagrams.MonoidalUndirectedWiringDiagrams:
  TheoryUntypedHypergraphDiagram, TheoryHypergraphDiagram

# Data structures
#################

@present TheoryRelationDiagram <: TheoryUntypedHypergraphDiagram begin
  Variable::Data
  variable::Attr(Junction,Variable)
end

const RelationDiagram = AbstractACSetType(TheoryRelationDiagram)
const UntypedRelationDiagram = ACSetType(TheoryRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

@present TheoryTypedRelationDiagram <: TheoryHypergraphDiagram begin
  Variable::Data
  variable::Attr(Junction,Variable)
end

const TypedRelationDiagram = ACSetType(TheoryTypedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

RelationDiagram{Name}(ports::Int) where {Name} =
  UntypedRelationDiagram{Name,Symbol}(ports)
RelationDiagram{Name}(ports::AbstractVector{T}) where {T,Name} =
  TypedRelationDiagram{T,Name,Symbol}(ports)

# Relations
###########

""" Construct an undirected wiring diagram using relation notation.

Unlike the `@program` macro for directed wiring diagrams, this macro
fundamentally alters the usual semantics of the Julia language. Function calls
with n arguments are now interpreted as assertions that an n-ary relation holds
at a particular point. For example, the operation of composing of binary
relations R ⊆ X × Y and S ⊆ Y × Z can be represented as an undirected wiring
diagram by the macro call

```julia
@relation (x,z) where (x::X, y::Y, z::Z) begin
  R(x,y)
  S(y,z)
end
```

In general, the context in the `where` clause defines the set of junctions in
the diagram and variable sharing defines the wiring of ports to junctions.
"""
macro relation(exprs...)
  :(parse_relation_diagram($((QuoteNode(expr) for expr in exprs)...)))
end

""" Parse an undirected wiring diagram from a relation expression.

For more information, see the corresponding macro [`@relation`](@ref).
"""
function parse_relation_diagram(expr::Expr)
  @match expr begin
    Expr(:function, head, body) => parse_relation_diagram(head, body)
    Expr(:->, head, body) => parse_relation_diagram(head, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_relation_diagram(head::Expr, body::Expr)
  body = Base.remove_linenums!(body)
  @match head begin
    Expr(:where, Expr(:tuple, args...), Expr(:tuple, context...)) =>
      make_relation_diagram(context, args, body.args)
    _ => error("Invalid syntax in declaration of outer ports and context")
  end
end

function make_relation_diagram(context::AbstractVector, args::AbstractVector,
                               body::AbstractVector)
  all_vars, all_types = parse_context(context)
  outer_vars = parse_variables(args)
  outer_vars ⊆ all_vars || error("One of variables $outer_vars is not declared")
  var_types = if isnothing(all_types) # Untyped case.
    vars -> length(vars)
  else # Typed case.
    var_type_map = Dict{Symbol,Symbol}(zip(all_vars, all_types))
    vars -> getindex.(Ref(var_type_map), vars)
  end

  # Create diagram and add outer ports and junctions.
  d = RelationDiagram{Symbol}(var_types(outer_vars))
  add_junctions!(d, var_types(all_vars), variable=all_vars)
  set_junction!(d, ports(d, outer=true),
                incident(d, outer_vars, :variable), outer=true)

  # Add boxes to diagram.
  for expr in body
    name, vars = @match expr begin
      Expr(:call, name::Symbol, vars...) => (name, parse_variables(vars))
      _ => error("Invalid syntax in box definition $expr")
    end
    vars ⊆ all_vars || error("One of variables $vars is not declared")
    box = add_box!(d, var_types(vars), name=name)
    set_junction!(d, ports(d, box), incident(d, vars, :variable))
  end

  return d
end

function parse_context(context)
  vars = map(context) do term
    @match term begin
      Expr(:(::), var::Symbol, type::Symbol) => (var => type)
      var::Symbol => var
      _ => error("Invalid syntax in term $expr of context")
    end
  end
  if vars isa AbstractVector{Symbol}
    (vars, nothing)
  elseif vars isa AbstractVector{Pair{Symbol,Symbol}}
    (first.(vars), last.(vars))
  else
    error("Context $context mixes typed and untyped terms")
  end
end

parse_variables(vars) = collect(Symbol, vars)

# Tensor networks
#################

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
    Expr(:tuple, args...) => parse_variables(args)
    Expr(:vect, args...) => parse_variables(args)
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
    Expr(:ref, name::Symbol, args...) => (name, parse_variables(args))
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

However,, the macros `@cast` and `@reduce` from
[TensorCast.jl](https://github.com/mcabbott/TensorCast.jl) will *not* work
because they do not support implicit summation.

See also: [`@tensor_network`](@ref), the "inverse" to this macro.
"""
macro eval_tensor_network(diagram, tensor_macro)
  # XXX: We cannot use `GeneralizedGenerated.mk_function` here because packages
  # like Tullio generate code with type parameters, which GG does not allow.
  # Thus we are stuck with `eval`. Of course, the real solution is for the Julia
  # tensor packages to expose a tensor contraction interface that is not based
  # on macros but on an appropriate data structure---such as wiring diagrams!
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

""" Parse relation expressions in Julia syntax into undirected wiring diagrams.
"""
module RelationalPrograms
export RelationDiagram, @relation, @tensor_network, parse_relation_diagram,
  parse_tensor_network, compile_tensor, compile_tensor_expr

using Compat
using GeneralizedGenerated: mk_function
using Match

using ...CategoricalAlgebra.CSets, ...Present
using ...Theories: FreeCategory
using ...WiringDiagrams.UndirectedWiringDiagrams
import ...WiringDiagrams.UndirectedWiringDiagrams: UndirectedWiringDiagram,
  TheoryUWD, TheoryTypedUWD

# Data structures
#################

@present TheoryRelationDiagram <: TheoryUWD begin
  Name::Ob
  name::Hom(Box,Name)
  variable::Hom(Junction,Name)
end

const RelationDiagram = AbstractCSetType(TheoryRelationDiagram, data=[:Name])
const UntypedRelationDiagram = CSetType(
  TheoryRelationDiagram, data=[:Name],
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

@present TheoryTypedRelationDiagram <: TheoryTypedUWD begin
  Name::Ob
  name::Hom(Box,Name)
  variable::Hom(Junction,Name)
end

const TypedRelationDiagram = CSetType(
  TheoryTypedRelationDiagram, data=[:Name, :Type],
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

function UndirectedWiringDiagram(::Type{RelationDiagram}, nports::Int)
  UndirectedWiringDiagram(UntypedRelationDiagram, nports,
                          name=Symbol, variable=Symbol)
end
function UndirectedWiringDiagram(::Type{RelationDiagram},
                                 port_types::AbstractVector{Symbol})
  UndirectedWiringDiagram(TypedRelationDiagram, port_types,
                          name=Symbol, variable=Symbol)
end

RelationDiagram(ports) = UndirectedWiringDiagram(RelationDiagram, ports)

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
  Expr(:call, GlobalRef(RelationalPrograms, :parse_relation_diagram),
       (QuoteNode(expr) for expr in exprs)...)
end

""" Parse an undirected wiring diagram from a relation expression.

For more information, see the corresponding macro [`@relation`](@ref).
"""
function parse_relation_diagram(expr::Expr)
  @match expr begin
    Expr(:function, [head, body]) => parse_relation_diagram(head, body)
    Expr(:->, [head, body]) => parse_relation_diagram(head, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_relation_diagram(head::Expr, body::Expr)
  body = Base.remove_linenums!(body)
  @match head begin
    Expr(:where, [Expr(:tuple, args), Expr(:tuple, context)]) =>
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
  d = RelationDiagram(var_types(outer_vars))
  add_junctions!(d, var_types(all_vars), variable=all_vars)
  set_junction!(d, ports(d, outer=true),
                incident(d, outer_vars, :variable), outer=true)

  # Add boxes to diagram.
  for expr in body
    name, vars = @match expr begin
      Expr(:call, [name::Symbol, vars...]) => (name, parse_variables(vars))
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
      Expr(:(::), [var::Symbol, type::Symbol]) => (var => type)
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

See also: [`compile_tensor`](@ref), the "inverse" to this macro.
"""
macro tensor_network(exprs...)
  Expr(:call, GlobalRef(RelationalPrograms, :parse_tensor_network),
       (QuoteNode(expr) for expr in exprs)...)
end

""" Parse an undirected wiring diagram from a tensor expression.

For more information, see the corresponding macro [`@tensor_network`](@ref).
"""
function parse_tensor_network(context::Expr, expr::Expr)
  all_vars = @match context begin
    Expr(:tuple, args) => parse_variables(args)
    Expr(:vect, args) => parse_variables(args)
  end
  parse_tensor_network(expr, all_vars=all_vars)
end

function parse_tensor_network(expr::Expr; all_vars=nothing)
  # Parse tensor expression.
  (outer_name, outer_vars), body = @match expr begin
    Expr(:(=), [outer, body]) => (parse_tensor_term(outer), body)
    Expr(:(:=), [outer, body]) => (parse_tensor_term(outer), body)
    _ => error("Tensor expression $expr must be an assignment, either = or :=")
  end
  names_and_vars = map(parse_tensor_term, @match body begin
    Expr(:call, [:(*), args...]) => args
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
  d = RelationDiagram(length(outer_vars))
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
    Expr(:ref, [name::Symbol, args...]) => (name, parse_variables(args))
    name::Symbol => (name, Symbol[]) # Scalar
    _ => error("Invalid syntax in term $expr in tensor expression")
  end
end

""" Compile tensor contraction function from undirected wiring diagram.

The arguments are an undirected wiring diagram and a macro compatible with the
notation for tensor contractions that is de facto standard among the Julia
tensor packages. For example,

```julia
f = compile_tensor(diagram, var"@tensor")
```

defines a contraction function using the `@tensor` macro. The following macros
should be supported:

- `@tensor` from
  [TensorOperations.jl](https://github.com/Jutho/TensorOperations.jl).
- `@tullio` from [Tullio.jl](https://github.com/mcabbott/Tullio.jl)
- `@einsum` from [Einsum.jl](https://github.com/ahwillia/Einsum.jl)
- `@ein` from [OMEinsum.jl](https://github.com/under-Peter/OMEinsum.jl)

For now, `@cast` and `@reduce` from
[TensorCast.jl](https://github.com/mcabbott/TensorCast.jl) are *not* supported
since they do not use implicit summation.

See also: [`@tensor_network`](@ref), the "inverse" to this function.
"""
function compile_tensor(d::UndirectedWiringDiagram, tensor_macro;
                        context::Bool=false, kw...)
  assign_expr, names, vars = compile_tensor_expr(d; kw...)
  expr = Expr(:function, Expr(:tuple, names...),
    Expr(:macrocall, macro_ref(tensor_macro), LineNumberNode(0),
         (context ? (Expr(:tuple, vars...),) : ())..., assign_expr))
  mk_function(expr)
end
macro_ref(m) = GlobalRef(parentmodule(m), nameof(m))
macro_ref(m::Symbol) = m

""" Generate tensor expression from undirected wiring diagram.

See also: [`compile_tensor`](@ref).
"""
function compile_tensor_expr(d::UndirectedWiringDiagram;
    assign_op::Symbol=:(:=), assign_name::Symbol=:out)
  names = has_subpart(d, :name) ? subpart(d, :name) :
    [ Symbol("A$i") for i in boxes(d) ]
  vars = has_subpart(d, :variable) ? subpart(d, :variable) :
    [ Symbol("i$j") for j in junctions(d) ]
  outer_vars = vars[junction(d, ports(d, outer=true), outer=true)]
  terms = map(boxes(d)) do box
    ref_expr(names[box], vars[junction(d, ports(d, box))])
  end
  lhs = ref_expr(assign_name, outer_vars)
  rhs = if isempty(terms); 1
    elseif length(terms) == 1; first(terms)
    else Expr(:call, :(*), terms...) end
  (Expr(assign_op, lhs, rhs), unique(names), vars)
end

function ref_expr(name::Symbol, vars)
  isempty(vars) ? name : Expr(:ref, name, vars...)
end

end

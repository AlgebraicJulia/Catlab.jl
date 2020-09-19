""" Generalized algebraic theories (GATs) in Julia.
"""
module GAT
export @theory, @signature, @instance, theory, invoke_term

using Base.Meta: ParseError
using Compat
using AutoHashEquals
using DataStructures: OrderedDict
using Logging
using MLStyle: @match

using ..Meta

# Data types
############

const Context = OrderedDict{Symbol,Expr0}

""" Type constructor in a GAT.
"""
@auto_hash_equals struct TypeConstructor
  name::Symbol
  params::Vector{Symbol}
  context::Context
  doc::Union{String,Nothing}

  function TypeConstructor(name::Symbol, params::Vector,
                           context::Context, doc=nothing)
    new(name, params, context, doc)
  end
end

""" Term constructor in a GAT.
"""
@auto_hash_equals struct TermConstructor
  name::Symbol
  params::Vector{Symbol}
  typ::Expr0
  context::Context
  doc::Union{String,Nothing}

  function TermConstructor(name::Symbol, params::Vector, typ::Expr0,
                           context::Context, doc=nothing)
    new(name, params, typ, context, doc)
  end
end

""" Axiom constructor in a GAT.
"""
@auto_hash_equals struct AxiomConstructor
  name::Symbol
  left::Expr0
  right::Expr0
  context::Context
  doc::Union{String,Nothing}

  function AxiomConstructor(name::Symbol, left::Expr0, right::Expr0,
                            context::Context, doc=nothing)
    new(name, left, right, context, doc)
  end
end

""" Data structure for a generalized algebraic theory (GAT).
"""
@auto_hash_equals struct Theory
  types::Vector{TypeConstructor}
  terms::Vector{TermConstructor}
  axioms::Vector{AxiomConstructor}
  aliases::Dict{Symbol,Symbol}
end

struct TheoryBinding
  name::Symbol
  params::Vector{Symbol}
end
struct TheoryHead
  main::TheoryBinding
  base::Vector{TheoryBinding}
  TheoryHead(main, base=[]) = new(main, base)
end

# Theories
##########

""" Define a generalized algebraic theory (GAT).

Four kinds of things can go in the theory body:

1. Type constructors, indicated by the special type `TYPE`, e.g.,
   `Hom(X::Ob,Y::Ob)::TYPE`
2. Term constructors, e.g.,
   `id(X::Ob)::Hom(X,X)`
3. Function aliases, e.g.,
   `@op Hom :→`
4. Equality axioms, e.g.,
   `f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))`

A theory can extend existing theories (at present only one).
"""
macro theory(head, body)
  theory_builder(head, body)
end

""" Define a signature for a generalized algebraic theory (GAT).

A signature is the same as a theory, except it may not contain axioms, and
therefore only three kinds of things can go in the signature body:

1. Type constructors, indicated by the special type `TYPE`, e.g.,
   `Hom(X::Ob,Y::Ob)::TYPE`
2. Term constructors, e.g.,
   `id(X::Ob)::Hom(X,X)`
3. Function aliases, e.g.,
   `@op Hom :→`

A signature can extend existing theories (at present only one).
"""
macro signature(head, body)
  theory_builder(head, body, signature=true)
end

""" Retrieve generalized algebraic theory associated with abstract type.

For example, if `Category` is imported from `Catlab.Theories`, then
`theory(Category)`returns the theory of a category.
"""
function theory end

""" Define how a theory is built, set up as a separate function to allow both
    the signature and theory macros to share code and throw an error if any
    axioms are defined in a signature.
"""
function theory_builder(head, body; signature=false)
  # Parse theory header.
  head = parse_theory_head(head)
  @assert all(param in head.main.params
              for base in head.base for param in base.params)
  @assert length(head.base) <= 1 "Multiple theory extension not supported"
  base_name = isempty(head.base) ? nothing : only(head.base).name

  # Parse theory body: GAT types/terms and function aliases.
  types, terms, axioms, aliases = parse_theory_body(body)
  if signature && length(axioms) > 0
    throw(ParseError("@signature macro does not allow axioms to be defined"))
  end
  theory = Theory(types, terms, axioms, aliases)

  # We must generate and evaluate the code at *run time* because the base
  # theory, if specified, is not available at *parse time*.
  expr = :(theory_code($head, $theory, $(esc(base_name))))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ $(esc(head.main.name))))
end

function theory_code(head, theory, base_type)
  # Add types/terms/aliases from base theory, if provided.
  if !isnothing(base_type)
    base_theory = GAT.theory(base_type)
    base_params = [ type.name for type in base_theory.types ]
    bindings = Dict(zip(base_params, only(head.base).params))
    base_theory = replace_types(bindings, base_theory)
    theory = Theory([base_theory.types; theory.types],
                    [base_theory.terms; theory.terms],
                    [base_theory.axioms; theory.axioms],
                    merge(base_theory.aliases, theory.aliases))
  end
  theory = replace_types(theory.aliases, theory)

  # Names of generic functions in interface defined by theory.
  names = unique!(vcat(
    [ param for type in theory.types for param in type.params ], # Accessors.
    [ term.name for term in theory.terms ], # Term constructors.
    collect(keys(theory.aliases)) # Unicode aliases.
  ))  
  
  # Generate block with abstract type definition, registration of theory,
  # and stubs for generic functions.
  Expr(:block,
    Expr(:abstract, head.main.name),
    Expr(:(=),
      Expr(:call, GlobalRef(GAT, :theory),
        Expr(:(::), Expr(:curly, :Type, head.main.name))),
      theory),
    (Expr(:function, name) for name in names)...,
  )
end

function parse_theory_head(expr::Expr)::TheoryHead
  parse = parse_theory_binding
  parse_jl = parse_theory_binding_jlstyle
  parse_either = parse_theory_binding_either
  @match expr begin
    (Expr(:call, :(=>), Expr(:tuple, bases), main)
      => TheoryHead(parse(main), map(parse, bases)))
    (Expr(:(<:), main, Expr(:tuple,bases))
      => TheoryHead(parse_jl(main), map(parse_jl, bases)))
    Expr(:call, :(=>), base, main) => TheoryHead(parse(main), [parse(base)])
    Expr(:(<:), main, base) => TheoryHead(parse_jl(main), [parse_jl(base)])
    _ => TheoryHead(parse_either(expr))
  end
end

function parse_theory_binding(expr::Expr)::TheoryBinding
  @warn "Using Haskell-style theory declaration with parentheses is deprecated," *
    " use Julia-style with curly braces."
  @match expr begin
    Expr(:call, name::Symbol, params...) => TheoryBinding(name, params)
    _ => throw(ParseError("Ill-formed theory binding $expr"))
  end
end

function parse_theory_binding_jlstyle(expr::Expr)::TheoryBinding
  @match expr begin
    Expr(:curly, name::Symbol, params...) => TheoryBinding(name, params)
    _ => throw(ParseError("Ill-formed theory binding $expr"))
  end
end

function parse_theory_binding_either(expr::Expr)::TheoryBinding
  @match expr begin
    Expr(:call, name::Symbol, params...) => TheoryBinding(name, params)
    Expr(:curly, name::Symbol, params...) => TheoryBinding(name, params)
    _ => throw(ParseError("Ill-formed theory binding $expr"))
  end
end

""" Parse the body of a GAT declaration.
"""
function parse_theory_body(expr::Expr)
  @assert expr.head == :block
  aliases = Dict{Symbol, Symbol}()
  types = OrderedDict{Symbol,TypeConstructor}()
  terms = TermConstructor[]
  axioms = AxiomConstructor[]
  for elem in strip_lines(expr).args
    elem = strip_lines(elem)
    head = last(parse_docstring(elem)).head
    if head in (:(::), :call, :comparison, :where)
      cons = parse_constructor(elem)
      if isa(cons, TypeConstructor)
        if haskey(types, cons.name)
          throw(ParseError("Duplicate type constructor $elem"))
        else
          types[cons.name] = cons
        end
      elseif isa(cons, TermConstructor)
        push!(terms, cons)
      else
        push!(axioms, cons)
      end
    elseif head == :macrocall && elem.args[1] == Symbol("@op")
      if elem.args[2].head == :(:=)
        aliases[elem.args[2].args[1]] = elem.args[2].args[2]
      elseif elem.args[2].head == :block
        merge!(aliases, Dict(map(x -> if x.head == :(:=)
                                        x.args[1] => x.args[2]
                                      else
                                        throw(ParseError("Ill-formed alias $x"))
                                      end, strip_lines(elem.args[2]).args)))
      else
        throw(ParseError("Ill-formed alias $elem"))
      end
    else
      throw(ParseError("Ill-formed theory element $elem"))
    end
  end
  return (collect(values(types)), terms, axioms, aliases)
end

""" Get type constructor by name.

Unlike term constructors, type constructors cannot be overloaded, so there is at
most one type constructor with a given name.
"""
function get_type(theory::Theory, name::Symbol)::TypeConstructor
  indices = findall(cons -> cons.name == name, theory.types)
  length(indices) == 1 || error("Malformed GAT definition type constructors cannot be overloaded $name")
  theory.types[indices[1]]
end
function has_type(theory::Theory, name::Symbol)::Bool
  findfirst(cons -> cons.name == name, theory.types) != nothing
end

""" Add a type-valued first argument to a Julia function signature.

We need this to avoid ambiguity in method dispatch when a term constructor has
no arguments (e.g., `munit()`) or more generally has no arguments that are types
in the signature (e.g., object generators in a category).

The fundamental reason why these cases must be treated specially is that Julia
does not (yet?) support
[dispatching on return type](https://github.com/JuliaLang/julia/issues/19206).
"""
function add_type_dispatch(call_expr::Expr, type_expr::Expr0)::Expr
  @match call_expr begin
    (Expr(:call, name, args...) =>
      Expr(:call, name, :(::Type{$type_expr}), args...))
    _ => throw(ParseError("Ill-formed call expression $call_expr"))
  end
end

# GAT expressions
#################

""" Parse a raw expression in a GAT.

A "raw expression" is a just composition of function and constant symbols.
"""
function parse_raw_expr(expr)
  @match expr begin
    Expr(:call, args...) => map(parse_raw_expr, args)
    head::Symbol => nothing
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
  expr # Return the expression unmodified. This function just checks syntax.
end

""" Parse context for term or type in a GAT.
"""
function parse_context(expr::Expr)::Context
  context = Context()
  args = expr.head == :tuple ? expr.args : [ expr ]
  for arg in args
    name, type = @match arg begin
      Expr(:(::), name::Symbol, type) => (name, parse_raw_expr(type))
      name::Symbol => (name, :Any)
      _ => throw(ParseError("Ill-formed context expression $expr"))
    end
    if haskey(context, name)
      throw(ParseError("Name $name already defined"))
    end
    context[name] = type
  end
  context
end

""" Parse type or term constructor in a GAT.
"""
function parse_constructor(expr::Expr)::Union{TypeConstructor,TermConstructor,
                                              AxiomConstructor}
  # Context is optional.
  doc, expr = parse_docstring(expr)
  cons_expr, context = @match expr begin
    Expr(:call, :<=, inner, context) => (inner, parse_context(context))
    Expr(:call, :⊣, inner, context) => (inner, parse_context(context))
    Expr(:comparison, cons_left, cons_sym, cons_right, :⊣, context) => (
      Expr(:call, cons_sym, cons_left, cons_right), parse_context(context))
    Expr(:where, inner, context) => (inner, parse_context(context))
    _ => (expr, Context())
  end

  # Allow abbreviated syntax where tail of context is included in parameters.
  function parse_param(param::Expr0)::Symbol
    name, type = @match param begin
      Expr(:(::), name::Symbol, type) => (name, parse_raw_expr(type))
      name::Symbol => (name, :Any)
      _ => throw(ParseError("Ill-formed type/term parameter $param"))
    end
    if !haskey(context, name)
      context[name] = type
    end
    name
  end

  @match cons_expr begin
    (Expr(:(::), name::Symbol, :TYPE)
      => TypeConstructor(name, [], context, doc))
    (Expr(:(::), Expr(:call, name::Symbol, params...), :TYPE)
      => TypeConstructor(name, map(parse_param, params), context, doc))
    (Expr(:(::), Expr(:call, name::Symbol, params...), type)
      => TermConstructor(name, map(parse_param, params), parse_raw_expr(type),
                         context, doc))
    (Expr(:call, :(==), left, right)
       => AxiomConstructor(:(==), left, right, context, doc))
    _ => throw(ParseError("Ill-formed type/term constructor $cons_expr"))
  end
end

""" Replace names of type constructors in a GAT.
"""
function replace_types(bindings::Dict, theory::Theory)::Theory
  Theory([ replace_types(bindings, t) for t in theory.types ],
         [ replace_types(bindings, t) for t in theory.terms ],
         [ replace_types(bindings, t) for t in theory.axioms ],
         replace_types(bindings, theory.aliases))
end
function replace_types(bindings::Dict, cons::TypeConstructor)::TypeConstructor
  TypeConstructor(replace_symbols(bindings, cons.name), cons.params,
                  replace_types(bindings, cons.context), cons.doc)
end
function replace_types(bindings::Dict, cons::TermConstructor)::TermConstructor
  TermConstructor(cons.name, cons.params,
                  replace_symbols(bindings, cons.typ),
                  replace_types(bindings, cons.context), cons.doc)
end
function replace_types(bindings::Dict, cons::AxiomConstructor)::AxiomConstructor
  AxiomConstructor(cons.name,
                   replace_symbols(bindings, cons.left),
                   replace_symbols(bindings, cons.right),
                   replace_types(bindings, cons.context), cons.doc)
end
function replace_types(bindings::Dict, aliases::Dict)::Dict
  Dict(a => replace_symbols(bindings, aliases[a])
       for a in keys(aliases))
end
function replace_types(bindings::Dict, context::Context)::Context
  GAT.Context(((name => @match expr begin
    (Expr(:call, sym::Symbol, args...) =>
      Expr(:call, replace_symbols(bindings, sym), args...))
    sym::Symbol => replace_symbols(bindings, sym)
  end) for (name, expr) in context))
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, head::Symbol, args...) => head
    sym::Symbol => sym
  end
end

# GAT expressions
#################

""" Expand context variables that occur implicitly in an expression.

Reference: (Cartmell, 1986, Sec 10: 'Informal syntax').
"""
function expand_in_context(expr, params::Vector{Symbol},
                           context::Context, theory::Theory)
  @match expr begin
    Expr(:call, name::Symbol, args...) => begin
      expanded = [expand_in_context(e, params, context, theory) for e in args]
      Expr(:call, name, expanded...)
    end
    name::Symbol => begin
      if name in params
        name
      elseif haskey(context, name)
        expand_symbol_in_context(name, params, context, theory)
      else
        error("Name $name missing from context $context")
      end
    end
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
end
function expand_symbol_in_context(sym::Symbol, params::Vector{Symbol},
                                  context::Context, theory::Theory)
  # This code expands symbols that occur as direct arguments to type
  # constructors. If there are term constructors in between, it does not work:
  # indeed, it cannot work in general because the term constructors are not
  # necessarily injective. For example, we can expand :X in
  #   (:X => :Ob, :f => :(Hom(X)))
  # but not in
  #   (:X => :Ob, :Y => :Ob, :f => :(Hom(otimes(X,Y))))
  names = collect(keys(context))
  start = findfirst(names .== sym)
  for name in names[start+1:end]
    expr = context[name]
    if isa(expr, Expr) && expr.head == :call && sym in expr.args[2:end]
      cons = get_type(theory, expr.args[1])
      accessor = cons.params[findfirst(expr.args[2:end] .== sym)]
      expanded = Expr(:call, accessor, name)
      return expand_in_context(expanded, params, context, theory)
    end
  end
  error("Name $sym does not occur explicitly among $params in context $context")
end

""" Expand context variables that occur implicitly in the type expression
of a term constructor.
"""
function expand_term_type(cons::TermConstructor, theory::Theory)
  isa(cons.typ, Symbol) ? cons.typ :
    expand_in_context(cons.typ, cons.params, cons.context, theory)
end

""" Implicit equations defined by a context.

This function allows a generalized algebraic theory (GAT) to be expressed as
an essentially algebraic theory, i.e., as partial functions whose domains are
defined by equations.

References:
 - (Cartmell, 1986, Sec 6: "Essentially algebraic theories and categories with
    finite limits")
 - (Freyd, 1972, "Aspects of topoi")
"""
function equations(context::Context, theory::Theory)::Vector{Pair}
  # The same restrictions as `expand_symbol_in_context` apply here.
  eqs = Pair[]
  names = collect(keys(context))
  for (start, var) in enumerate(names)
    for name in names[start+1:end]
      expr = context[name]
      if isa(expr, Symbol) && !has_type(theory, expr)
        # If the constructor is a symbol and there isn't a matching type in
        # the theory, assume it's a Julia type. For now, these are
        # completely ignored by the syntax system.
        continue
      end
      expr = isa(expr, Symbol) ? Expr(:call, expr) : expr
      cons = get_type(theory, expr.args[1])
      accessors = cons.params[findall(expr.args[2:end] .== var)]
      append!(eqs, (Expr(:call, a, name) => var for a in accessors))
    end
  end
  eqs
end

""" Implicit equations defined by context, allowing for implicit variables.
"""
function equations(params::Vector{Symbol}, context::Context,
                   theory::Theory)::Vector{Pair}
  eqs = [ (expand_in_context(lhs, params, context, theory) =>
           expand_in_context(rhs, params, context, theory))
          for (lhs, rhs) in equations(context, theory) ]
  # Remove tautologies (expr == expr) resulting from expansions.
  # FIXME: Should we worry about redundancies from the symmetry of equality,
  # i.e., (expr1 == expr2) && (expr2 == expr1)?
  filter(eq -> eq.first != eq.second, eqs)
end

""" Implicit equations for term constructor.
"""
function equations(cons::TermConstructor, theory::Theory)::Vector{Pair}
  equations(cons.params, cons.context, theory)
end

# Instances
###########

""" Define an *instance* of a generalized algebraic theory (GAT).
"""
macro instance(head, body)
  # Parse the instance definition.
  head = parse_theory_binding_either(head)
  functions, ext_functions = parse_instance_body(body)

  # We must generate and evaluate the code at *run time* because the theory
  # type is not defined at *parse time*.
  # Also, we "throw away" any docstring.
  # FIXME: Is there a better place to put the docstring?
  expr = :(instance_code($(esc(head.name)), $(esc(head.params)), $functions, $ext_functions))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ abstract type $(esc(gensym(:instance_doc))) end)) # /dev/null
end
function instance_code(theory_type, instance_types, instance_fns, external_fns)
  code = Expr(:block)
  theory = GAT.theory(theory_type)
  bindings = Dict(zip([type.name for type in theory.types], instance_types))
  bound_fns = [ replace_symbols(bindings, f) for f in interface(theory) ]
  bound_fns = OrderedDict(parse_function_sig(f) => f for f in bound_fns)
  instance_fns = Dict(parse_function_sig(f) => f for f in instance_fns)
  for (sig, f) in bound_fns
    if sig.name in external_fns
      continue
    elseif haskey(instance_fns, sig)
      f_impl = instance_fns[sig]
    elseif !isnothing(f.impl)
      f_impl = f
    else
      error("Method $(f.call_expr) not implemented in $(nameof(mod)) instance")
    end
    push!(code.args, generate_function(f_impl))
  end
  return code
end

""" Parse the body of a GAT instance definition.
"""
function parse_instance_body(expr::Expr)
  @assert expr.head == :block
  funs = JuliaFunction[]
  ext_funs = Symbol[]
  for elem in strip_lines(expr).args
    elem = strip_lines(elem)
    head = elem.head
    if head == :macrocall && elem.args[1] == Symbol("@import")
      ext_funs = @match elem.args[2] begin
        sym::Symbol => [ext_funs; [sym]]
        Expr(:tuple, args...) => [ext_funs; Symbol[args...]]
      end
    else
      push!(funs, parse_function(elem))
    end
  end
  return (funs, ext_funs)
end

""" Complete set of Julia functions for a theory.
"""
function interface(theory::Theory)::Vector{JuliaFunction}
  [ accessors(theory);
    constructors(theory);
    alias_functions(theory) ]
end

""" Julia functions for type parameter accessors.
"""
function accessors(theory::Theory)::Vector{JuliaFunction}
  vcat(map(accessors, theory.types)...)
end
function accessors(cons::TypeConstructor)::Vector{JuliaFunction}
  [ JuliaFunction(Expr(:call, param, Expr(:(::), cons.name)),
                  strip_type(cons.context[param]))
    for param in cons.params ]
end

""" Julia functions for term constructors of GAT.
"""
function constructors(theory::Theory)::Vector{JuliaFunction}
  [ constructor(cons, theory) for cons in theory.terms ]
end
function constructor(cons::Union{TypeConstructor,TermConstructor},
                     theory::Theory)::JuliaFunction
  arg_names = cons.params
  arg_types = [ strip_type(cons.context[name]) for name in arg_names ]
  args = [ Expr(:(::), name, typ) for (name,typ) in zip(arg_names, arg_types) ]
  return_type = cons isa TermConstructor ? strip_type(cons.typ) : cons.name

  call_expr = Expr(:call, cons.name, args...)
  if !any(has_type(theory, typ) for typ in arg_types)
    call_expr = add_type_dispatch(call_expr, return_type)
  end
  JuliaFunction(call_expr, return_type)
end

""" Julia functions for term and type aliases of GAT.
"""
function alias_functions(theory::Theory)::Vector{JuliaFunction}
  # collect all of the types and terms from the theory
  terms_types = [theory.types; theory.terms]
  # iterate over the specified aliases
  collect(Iterators.flatten(map(collect(theory.aliases)) do alias
    # collect all of the destination function definitions to alias
    # allows an alias to overite all the type definitions of a function
    dests = filter(i -> i.name == last(alias), map(x -> x, terms_types))
    # If there are no matching functions, throw a parse error
    if isempty(dests)
      throw(ParseError("Cannot alias undefined type or term $alias"))
    end
    # For each destination, create a Julia function
    map(dests) do dest
      fun = constructor(dest, theory)
      fun.call_expr.args[1] = first(alias)
      # Extract arguments from function header, handling special case of
      # created by `add_type_dispatch`.
      args = map(fun.call_expr.args[2:end]) do arg
        @match arg begin
          # Special case: dispatch on return type.
          Expr(:(::), Expr(:curly, :Type, type)) => type
          # Main case: typed parameter.
          Expr(:(::), param, type) => param
          _ => throw(ParseError("Cannot parse argument $arg for alias $alias"))
        end
      end
      body = Expr(:call, dest.name, args...)
      JuliaFunction(fun.call_expr, fun.return_type, body)
    end
  end))
end

""" Invoke a term constructor by name on an instance.

This method provides reflection for GATs. In everyday use the generic
method for the constructor should be called directly, not through this function.

Cf. Julia's builtin `invoke()` function.
"""
function invoke_term(theory_type::Type, instance_types::Tuple,
                     constructor_name::Symbol, args...)
  # Get the corresponding Julia method from the parent module.
  method = getfield(parentmodule(theory_type), constructor_name)
  args = collect(Any, args)

  # Add dispatch on return type, if necessary.
  if !any(typeof(arg) <: typ for typ in instance_types for arg in args)
    # Case 1: Name refers to type constructor, e.g., generator constructor
    # in syntax system.
    theory = GAT.theory(theory_type)
    index = findfirst(cons -> cons.name == constructor_name, theory.types)
    if isnothing(index)
      # Case 2: Name refers to term constructor.
      # FIXME: Terms constructors can be overloaded, so there may be multiple
      # term constructors with the same name. Distinguishing them requires type
      # inference. I am punting on that right now.
      constructor = theory.terms[
        findfirst(cons -> cons.name == constructor_name, theory.terms)]
      return_name = strip_type(constructor.typ)
      index = findfirst(cons -> cons.name == return_name, theory.types)
    end
    insert!(args, 1, instance_types[index])
  end

  # Invoke the method!
  method(args...)
end

end

""" Generalized algebraic theories (GATs) in Julia.

At present, this module only supports defining the *signature* of a GAT. In the
future we may allow *axioms* to be expressed as well. Regardless, we will
persist in calling this module "GAT". Signatures are defined using the
`@signature` macro.
"""
module GAT
export @signature, @instance, invoke_term

using Base.Meta: ParseError
using Compat
using AutoHashEquals
using DataStructures: OrderedDict
using Match

using ..Meta

# Data types
############

""" Base type for method stubs in GAT signature.
"""
abstract type Stub end

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

""" Signature for a generalized algebraic theory (GAT).
"""
@auto_hash_equals struct Signature
  types::Vector{TypeConstructor}
  terms::Vector{TermConstructor}
  axioms::Vector{AxiomConstructor}
  aliases::Dict{Symbol, Symbol}
end

""" Typeclass = GAT signature + Julia-specific content.
"""
struct Typeclass
  name::Symbol
  type_params::Vector{Symbol}
  signature::Signature
  functions::Vector{JuliaFunction}
end

struct SignatureBinding
  name::Symbol
  params::Vector{Symbol}
end
struct SignatureHead
  main::SignatureBinding
  base::Vector{SignatureBinding}
  SignatureHead(main, base=[]) = new(main, base)
end

# Signatures
############

""" Define a signature of a generalized algebraic theory (GAT).

Three kinds of things can go in the signature body:

1. Type constructors, indicated by the special type `TYPE`, e.g.
   `Hom(X::Ob,Y::Ob)::TYPE`
2. Term constructors, e.g.,
   `id(X::Ob)::Hom(X,X)`
3. Julia functions operating on the term constructors to provide additional
   functionality

A signature can extend existing signatures (at present only one).
"""
macro signature(head, body)
  # Parse signature header.
  head = parse_signature_head(head)
  @assert length(head.base) <= 1 "Multiple signature extension not supported"
  if length(head.base) == 1
    base_name, base_params = head.base[1].name, head.base[1].params
    @assert all(p in head.main.params for p in base_params)
  else
    base_name, base_params = nothing, []
  end

  # Parse signature body: GAT types/terms and extra Julia functions.
  types, terms, functions, axioms, aliases = parse_signature_body(body)
  signature = Signature(types, terms, axioms, aliases)
  class = Typeclass(head.main.name, head.main.params, signature, functions)

  # We must generate and evaluate the code at *run time* because the base
  # signature, if specified, is not available at *parse time*.
  expr = :(signature_code($class, $(esc(base_name)), $base_params))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ $(esc(head.main.name))))
end
function signature_code(main_class, base_mod, base_params)
  # TODO: Generate code to do something with main_class.signature.axioms
  # Add types/terms/functions from base class, if provided.
  main_sig = main_class.signature
  if isnothing(base_mod)
    class = main_class
  else
    base_class = base_mod.class()
    bindings = Dict(zip(base_class.type_params, base_params))
    base_sig = replace_types(bindings, base_class.signature)
    sig = Signature([base_sig.types; main_sig.types],
                    [base_sig.terms; main_sig.terms],
                    [base_sig.axioms; main_sig.axioms],
                    merge(base_sig.aliases, main_sig.aliases))
    functions = [ [ replace_symbols(bindings, f) for f in base_class.functions ];
                  main_class.functions ]
    class = Typeclass(main_class.name, main_class.type_params, sig, functions)
  end
  signature = replace_types(class.signature.aliases, class.signature)
  class = Typeclass(class.name, class.type_params, signature, class.functions)

  # Generate module with stub types.
  mod = Expr(:module, true, class.name,
    Expr(:block, [
      # Prevents error about export not being at toplevel.
      # https://github.com/JuliaLang/julia/issues/28991
      LineNumberNode(0);
      Expr(:export, [cons.name for cons in signature.types]...);
      map(gen_abstract_type, signature.types);
      :(class() = $(class));
    ]...))

  # Generate method stubs.
  # (We put them outside the module, so the stub type names must be qualified.)
  bindings = Dict(cons.name => Expr(:(.), class.name, QuoteNode(cons.name))
                  for cons in signature.types)
  fns = interface(class)

  toplevel = [ generate_function(replace_symbols(bindings, f)) for f in fns ]

  # Modules must be at top level:
  # https://github.com/JuliaLang/julia/issues/21009
  Expr(:toplevel, mod, toplevel...)
end

function parse_signature_head(expr::Expr)::SignatureHead
  parse = parse_signature_binding
  @match expr begin
    (Expr(:call, [:(=>), Expr(:tuple, bases), main])
      => SignatureHead(parse(main), map(parse, bases)))
    Expr(:call, [:(=>), base, main]) => SignatureHead(parse(main), [parse(base)])
    _ => SignatureHead(parse(expr))
  end
end

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...]) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature binding $expr"))
  end
end

""" Parse the body of a GAT signature declaration.
"""
function parse_signature_body(expr::Expr)
  @assert expr.head == :block
  aliases = Dict{Symbol, Symbol}()
  types = OrderedDict{Symbol,TypeConstructor}()
  terms = TermConstructor[]
  axioms = AxiomConstructor[]
  funs = JuliaFunction[]
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
    elseif head in (:(=), :function)
      push!(funs, parse_function(elem))
    elseif head == :macrocall && elem.args[1] == Symbol("@op")
      aliases[elem.args[3].value] = elem.args[2]
    else
      throw(ParseError("Ill-formed signature element $elem"))
    end
  end
  return (collect(values(types)), terms, funs, axioms, aliases)
end

""" Julia functions for type parameter accessors.
"""
function accessors(sig::Signature)::Vector{JuliaFunction}
  vcat(map(accessors, sig.types)...)
end
function accessors(cons::TypeConstructor)::Vector{JuliaFunction}
  [ JuliaFunction(Expr(:call, param, Expr(:(::), cons.name)),
                  strip_type(cons.context[param]))
    for param in cons.params ]
end

""" Julia functions for term constructors of GAT.
"""
function constructors(sig::Signature)::Vector{JuliaFunction}
  [ constructor(cons, sig) for cons in sig.terms ]
end
function constructor(cons::Union{TypeConstructor,TermConstructor},
                     sig::Signature)::JuliaFunction
  arg_names = cons.params
  arg_types = [ strip_type(cons.context[name]) for name in arg_names ]
  args = [ Expr(:(::), name, typ) for (name,typ) in zip(arg_names, arg_types) ]
  return_type = cons isa TermConstructor ? strip_type(cons.typ) : cons.name

  call_expr = Expr(:call, cons.name, args...)
  if !any(has_type(sig, typ) for typ in arg_types)
    call_expr = add_type_dispatch(call_expr, return_type)
  end
  JuliaFunction(call_expr, return_type)
end

""" Julia functions for term and type aliases of GAT.
"""
function alias_functions(sig::Signature)::Vector{JuliaFunction}
  # collect all of the types and terms from the signature
  terms_types = [sig.types; sig.terms]
  # iterate over the specified aliases
  collect(Iterators.flatten(map(collect(sig.aliases)) do alias
    # collect all of the destination function definitions to alias
    # allows an alias to overite all the type definitions of a function
    dests = filter(i -> i.name == last(alias), map(x -> x, terms_types))
    # If there are no matching functions, throw a parse error
    if isempty(dests)
      throw(ParseError("Cannot alias undefined type or term $dest"))
    end
    # For each destination, create a Julia function
    map(dests) do dest
      fun = constructor(dest, sig)
      fun.call_expr.args[1] = first(alias)
      # Extract arguments from function header, handling special case of
      # created by `add_type_dispatch`.
      args = map(fun.call_expr.args[2:end]) do arg
        @match arg begin
          # Special case: dispatch on return type.
          Expr(:(::), [ Expr(:curly, [:Type, type]) ]) => type
          # Main case: typed parameter.
          Expr(:(::), [ param, type ]) => param
          _ => throw(ParseError("Cannot parse argument $arg for alias $alias"))
        end
      end
      body = Expr(:call, dest.name, args...)
      JuliaFunction(fun.call_expr, fun.return_type, body)
    end
  end))
end

""" Complete set of Julia functions for a type class.
"""
function interface(class::Typeclass)::Vector{JuliaFunction}
  [ accessors(class.signature);
    constructors(class.signature);
    alias_functions(class.signature);
    class.functions ]
end

""" Get type constructor by name.

Unlike term constructors, type constructors cannot be overloaded, so there is at
most one type constructor with a given name.
"""
function get_type(sig::Signature, name::Symbol)::TypeConstructor
  indices = findall(cons -> cons.name == name, sig.types)
  @assert length(indices) == 1
  sig.types[indices[1]]
end
function has_type(sig::Signature, name::Symbol)::Bool
  findfirst(cons -> cons.name == name, sig.types) != nothing
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
    (Expr(:call, [name, args...]) =>
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
    Expr(:call, args) => map(parse_raw_expr, args)
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
    name, typ = @match arg begin
      Expr(:(::), [name::Symbol, typ]) => (name, parse_raw_expr(typ))
      _ => throw(ParseError("Ill-formed context expression $expr"))
    end
    push_context!(context, name, typ)
  end
  return context
end
function push_context!(context, name, expr)
  if haskey(context, name)
    throw(ParseError("Name $name already defined"))
  end
  context[name] = expr
end

""" Parse type or term constructor in a GAT.
"""
function parse_constructor(expr::Expr)::Union{TypeConstructor,TermConstructor,
                                              AxiomConstructor}
  # Context is optional.
  doc, expr = parse_docstring(expr)
  cons_expr, context = @match expr begin
    Expr(:call, [:<=, inner, context]) => (inner, parse_context(context))
    Expr(:call, [:⊣, inner, context]) => (inner, parse_context(context))
    Expr(:comparison, [cons_left, cons_sym, cons_right, :⊣, context]) => (
      Expr(:call, cons_sym, cons_left, cons_right), parse_context(context))
    Expr(:where, [inner, context]) => (inner, parse_context(context))
    _ => (expr, Context())
  end

  # Allow abbreviated syntax where tail of context is included in parameters.
  function parse_param(param::Expr0)::Symbol
    @match param begin
      Expr(:(::), [name::Symbol, typ]) => begin
        push_context!(context, name, parse_raw_expr(typ))
        name
      end
      name::Symbol => name
      _ => throw(ParseError("Ill-formed type/term parameter $param"))
    end
  end

  @match cons_expr begin
    (Expr(:(::), [name::Symbol, :TYPE])
      => TypeConstructor(name, [], context, doc))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...]), :TYPE])
      => TypeConstructor(name, map(parse_param, params), context, doc))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...]), typ])
      => TermConstructor(name, map(parse_param, params), parse_raw_expr(typ),
                         context, doc))
    (Expr(:call, [:(==), left, right]) => AxiomConstructor(:(==), left, right,
                         context, doc))
    _ => throw(ParseError("Ill-formed type/term constructor $cons_expr"))
  end
end

""" Generate abstract type definition from a GAT type constructor.
"""
function gen_abstract_type(cons::TypeConstructor)::Expr
  stub_name = GlobalRef(GAT, :Stub)
  expr = :(abstract type $(cons.name) <: $stub_name end)
  generate_docstring(expr, cons.doc)
end

""" Replace names of type constructors in a GAT.
"""
function replace_types(bindings::Dict, sig::Signature)::Signature
  Signature([ replace_types(bindings, t) for t in sig.types ],
            [ replace_types(bindings, t) for t in sig.terms ],
            [ replace_types(bindings, t) for t in sig.axioms ],
            replace_types(bindings, sig.aliases))
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
    (Expr(:call, [sym::Symbol, args...]) =>
      Expr(:call, replace_symbols(bindings, sym), args...))
    sym::Symbol => replace_symbols(bindings, sym)
  end) for (name, expr) in context))
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, [head::Symbol, args...]) => head
    sym::Symbol => sym
  end
end

# GAT expressions in a signature
################################

""" Expand context variables that occur implicitly in an expression.

Reference: (Cartmell, 1986, Sec 10: 'Informal syntax').
"""
function expand_in_context(expr, params::Vector{Symbol},
                           context::Context, sig::Signature)
  @match expr begin
    Expr(:call, [name::Symbol, args...]) => begin
      expanded = [expand_in_context(e, params, context, sig) for e in args]
      Expr(:call, name, expanded...)
    end
    name::Symbol => begin
      if name in params
        name
      elseif haskey(context, name)
        expand_symbol_in_context(name, params, context, sig)
      else
        error("Name $name missing from context $context")
      end
    end
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
end
function expand_symbol_in_context(sym::Symbol, params::Vector{Symbol},
                                  context::Context, sig::Signature)
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
      cons = get_type(sig, expr.args[1])
      accessor = cons.params[findfirst(expr.args[2:end] .== sym)]
      expanded = Expr(:call, accessor, name)
      return expand_in_context(expanded, params, context, sig)
    end
  end
  error("Name $sym does not occur explicitly among $params in context $context")
end

""" Expand context variables that occur implicitly in the type expression
of a term constructor.
"""
function expand_term_type(cons::TermConstructor, sig::Signature)
  isa(cons.typ, Symbol) ? cons.typ :
    expand_in_context(cons.typ, cons.params, cons.context, sig)
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
function equations(context::Context, sig::Signature)::Vector{Pair}
  # The same restrictions as `expand_symbol_in_context` apply here.
  eqs = Pair[]
  names = collect(keys(context))
  for (start, var) in enumerate(names)
    for name in names[start+1:end]
      expr = context[name]
      if isa(expr, Symbol) && !has_type(sig, expr)
        # If the constructor is a symbol and there isn't a matching type in
        # the signature, assume it's a Julia type. For now, these are
        # completely ignored by the syntax system.
        continue
      end
      expr = isa(expr, Symbol) ? Expr(:call, expr) : expr
      cons = get_type(sig, expr.args[1])
      accessors = cons.params[findall(expr.args[2:end] .== var)]
      append!(eqs, (Expr(:call, a, name) => var for a in accessors))
    end
  end
  eqs
end

""" Implicit equations defined by context, allowing for implicit variables.
"""
function equations(params::Vector{Symbol}, context::Context,
                   sig::Signature)::Vector{Pair}
  eqs = [ (expand_in_context(lhs, params, context, sig) =>
           expand_in_context(rhs, params, context, sig))
          for (lhs, rhs) in equations(context, sig) ]
  # Remove tautologies (expr == expr) resulting from expansions.
  # FIXME: Should we worry about redundancies from the symmetry of equality,
  # i.e., (expr1 == expr2) && (expr2 == expr1)?
  filter(eq -> eq.first != eq.second, eqs)
end

""" Implicit equations for term constructor.
"""
function equations(cons::TermConstructor, sig::Signature)::Vector{Pair}
  equations(cons.params, cons.context, sig)
end

# Instances
###########

""" Define an *instance* of a generalized algebraic theory (GAT).

These are perfectly analagous to instances of a type class in Haskell. See also
the Typeclass.jl library for Julia.
"""
macro instance(head, body)
  # Parse the instance definition.
  head = parse_signature_binding(head)
  functions, ext_functions = parse_instance_body(body)

  # We must generate and evaluate the code at *run time* because the signature
  # module is not defined at *parse time*.
  # Also, we "throw away" any docstring.
  # FIXME: Is there a better place to put the docstring?
  expr = :(instance_code($(esc(head.name)), $(esc(head.params)), $functions, $ext_functions))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ abstract type $(esc(gensym(:instance_doc))) end)) # /dev/null
end
function instance_code(mod, instance_types, instance_fns, external_fns)
  code = Expr(:block)
  class = mod.class()
  bindings = Dict(zip(class.type_params, instance_types))
  bound_fns = [ replace_symbols(bindings, f) for f in interface(class) ]
  bound_fns = OrderedDict(parse_function_sig(f) => f for f in bound_fns)
  instance_fns = Dict(parse_function_sig(f) => f for f in instance_fns)
  for (sig, f) in bound_fns
    if haskey(instance_fns, sig)
      f_impl = instance_fns[sig]
    elseif !isnothing(f.impl)
      f_impl = f
    elseif f.call_expr.args[1] in external_fns
      continue
    else
      @error "Method $(f.call_expr) not implemented in $(class.name) instance"
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
        Expr(:tuple, arr) => [ext_funs; Symbol[arr...]]
      end
    else
      push!(funs, parse_function(elem))
    end
  end
  return (funs, ext_funs)
end

""" Invoke a term constructor by name on an instance.

This method provides reflection for GAT signatures. In everyday use the generic
method for the constructor should be called directly, not through this function.

Cf. Julia's builtin `invoke()` function.
"""
function invoke_term(signature_module::Module, instance_types::Tuple,
                     constructor_name::Symbol, args...)
  # Get the corresponding Julia method from the parent module.
  method = getfield(parentmodule(signature_module), constructor_name)
  args = collect(Any, args)

  # Add dispatch on return type, if necessary.
  if !any(typeof(arg) <: typ for typ in instance_types for arg in args)
    # Case 1: Name refers to type constructor, e.g., generator constructor
    # in syntax system.
    signature = signature_module.class().signature
    index = findfirst(cons -> cons.name == constructor_name, signature.types)
    if isnothing(index)
      # Case 2: Name refers to term constructor.
      # FIXME: Terms constructors can be overloaded, so there may be multiple
      # term constructors with the same name. Distinguishing them requires type
      # inference. I am punting on that right now.
      constructor = signature.terms[
        findfirst(cons -> cons.name == constructor_name, signature.terms)]
      return_name = strip_type(constructor.typ)
      index = findfirst(cons -> cons.name == return_name, signature.types)
    end
    insert!(args, 1, instance_types[index])
  end

  # Invoke the method!
  method(args...)
end

end

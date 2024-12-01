using MLStyle
using GATlab.Syntax: Ident, GAT, AlgSort
using GATlab.Util: Expr0
using GATlab.Syntax.TheoryInterface: WithModel
using GATlab.Models.SymbolicModels: symbolic_structs, internal_accessors,
  internal_constructors, symbolic_instance_methods
using GATlab.Models.ModelInterface: args_from_sorts, generate_instance,
  parse_model_param

const iflatten = Iterators.flatten


GATlab.getvalue(m::WithModel) = m.model

"""
Create an @instance for a model `M` whose methods are determined by type 
dispatch, e.g.:

```
@instance ThCategory{O,H} [model::M] begin
  id(x::O) = id(x)
  compose(f::H, g::H)::H = compose(f, g)
end
```

Use this with caution! For example, using this with two different models of 
the same theory with the same types would cause a conflict.
"""
function default_instance(theorymodule, theory, jltype_by_sort, model)
  acc = iflatten(values.(values(theory.accessors)))

  termcon_funs = map(last.(termcons(theory)) ∪ acc) do x 
    generate_function(use_dispatch_method_impl(x, theory, jltype_by_sort))
  end
  generate_instance(
    theory, theorymodule, jltype_by_sort, model, [], 
    Expr(:block, termcon_funs...); typecheck=true, escape=true)
end

"""
Create an @instance for a model `M` whose methods are determined by the 
implementation of another model, `M2`, e.g.:

```
@instance ThCategory{O,H} [model::M] begin
  id(x::O) = id(x)
  compose(f::H, g::H)::H = compose[M2](f, g)
end
```
"""
function default_model(theorymodule, theory, jltype_by_sort, model, model2)
  acc = iflatten(values.(values(theory.accessors)))
  termcon_funs = map(last.(termcons(theory)) ∪ acc) do x 
    generate_function(use_model_method_impl(x, theory, jltype_by_sort, model2))
  end
  generate_instance(
    theory, theorymodule, jltype_by_sort, model, [], 
    Expr(:block, termcon_funs...); typecheck=true, escape=true)
end

macro default_model(head, model)
  # Parse the head of @instance to get theory and instance types
  # TODO: should we allow instance types to be nothing? Is this in Catlab?
  (theory_module, instance_types) = @match head begin
    :($ThX{$(Ts...)}) => (ThX, Ts)
    _ => error("invalid syntax for head of @instance macro: $head")
  end

  # Get the underlying theory
  theory = macroexpand(__module__, :($theory_module.Meta.@theory))

  # A dictionary to look up the Julia type of a type constructor from its name (an ident)
  jltype_by_sort = Dict{AlgSort,Expr0}([
    zip(primitive_sorts(theory), instance_types)..., 
    [s => nameof(headof(s)) for s in struct_sorts(theory)]...
  ]) 

  # Get the model type that we are overloading for, or nothing if this is the
  # default instance for `instance_types`
  (m1, m2) = @match model begin
    Expr(:call, :(=>), x , y) => (y,x)
    _ => (nothing, parse_model_param(model)[1])
  end

  # Create the actual instance
  default_model(theory_module, theory, jltype_by_sort, m1, m2)
end

"""
A canonical implementation that just calls the method with type dispatch.
"""
function use_dispatch_method_impl(x::Ident, theory::GAT, 
                                  jltype_by_sort::Dict{AlgSort})
  op = getvalue(theory[x])
  name = nameof(getdecl(op))
  return_type = op isa AlgAccessor ? nothing : jltype_by_sort[AlgSort(op.type)]
  args = args_from_sorts(sortsignature(op), jltype_by_sort)
  impl = :(return $(name)($(args...)))
  JuliaFunction(name=name, args=args, return_type=return_type, impl=impl)
end

"""
A canonical implementation that just calls the method with the implementation
of another model, `m`.
"""
function use_model_method_impl(x::Ident, theory::GAT, 
                               jltype_by_sort::Dict{AlgSort}, m::Expr0)
  op = getvalue(theory[x])
  name = nameof(getdecl(op))
  return_type = op isa AlgAccessor ? nothing : jltype_by_sort[AlgSort(op.type)]
  args = args_from_sorts(sortsignature(op), jltype_by_sort)
  impl = :(return $(name)[$m()]($(args...)))
  JuliaFunction(name=name, args=args, return_type=return_type, impl=impl)
end

abstract type SymModel{T} <: Model{T} end 

"""
This version adds Part 1.5 and corresponding model Meta.M.
When upstreaming, we replace the implementation in Catlab
"""
macro symbolic_model(decl, theoryname, body)
  # Part 0: Parsing input
  
  theory = macroexpand(__module__, :($theoryname.Meta.@theory))
  
  (name, abstract_types) = @match decl begin
    Expr(:curly, name, abstract_types...) => (name, abstract_types)
    _ => throw(ParseError("Ill-formed head of @symbolic_model $decl"))
  end

  overrides = Dict{Ident, JuliaFunction}()

  if !isnothing(body)
    body.head == :block || error("expected a block as the body of @symbolic_model")

    for line in body.args
      if line isa LineNumberNode
        continue
      end
      f = parse_function(line)
      juliasig = parse_function_sig(f)
      decl = ident(theory; name=juliasig.name)
      sig = fromexpr.(Ref(GATContext(theory)), juliasig.types, Ref(AlgSort))
      method = resolvemethod(theory.resolvers[decl], sig)
      overrides[method] = f
    end
  end

  theorymodule = :($__module__.$theoryname)

  # Part 1: Generating structs

  module_structs = symbolic_structs(theory, abstract_types, __module__)

  # Part 1.5: Generate a model
  # mod_params = [Expr(:., __module__, QuoteNode(t)) for t in abstract_types ]
  # mod_params = [Expr(:., Expr(:call, :parentmodule, name), 
  #                    QuoteNode(nameof(t))) for t in theory.sorts ]
  mod_params = nameof.(theory.sorts)
  jltype_by_sort = Dict(zip(sorts(theory), mod_params))
  instance_code = default_instance(theorymodule, theory, jltype_by_sort, :M)
  imps = [theoryname, nameof.(theory.sorts)...]
  imp = Expr(:import, Expr(:(:), Expr(:(.), :(.),:(.), name), 
    [Expr(:(.), n) for n in [theoryname; nameof.(theory.sorts)]]...))

  # Part 2: Generating internal methods

  module_methods = [internal_accessors(theory)..., 
                    internal_constructors(theory, theorymodule)...]

  module_decl = :(module $(esc(name))
    export $(nameof.(sorts(theory))...)
    using ..($(nameof(__module__)))
    import ..($(nameof(__module__))): $theoryname
    using GATlab: @instance

    $(module_structs...)

    module $(esc(:Meta))
      $imp
      const $(esc(:theory_module)) = $(esc(theoryname))
      const $(esc(:theory)) = $(theory)
      const $(esc(:theory_type)) = $(esc(theoryname)).Meta.T
      # Canonical symbolic model
      struct M <: SymModel{Tuple{$(esc.(mod_params)...)}} end
      using ..$(theoryname)
      $instance_code
    end

    $(generate_function.(module_methods)...)


  end)

  # Part 3: Generating instance of theory
  theory_overloads = symbolic_instance_methods(theory, theoryname, name, overrides)

  alias_overloads = ModelInterface.make_alias_definitions(
    theory,
    theoryname,
    Dict(sort => :($name.$(nameof(sort))) for sort in sorts(theory)),
    nothing,
    [],
    []
  )

  Expr(
    :toplevel,
    module_decl,
    :(Core.@__doc__ $(esc(name))),
    esc.(generate_function.([theory_overloads; alias_overloads]))...,
  )
end

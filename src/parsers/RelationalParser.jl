"""    RelationalParser

Parsing UWD Structure with PEG.jl. and SyntacticModels. Allows us to
create a more modular grammar for RelationalProgram DSL.
"""
module RelationalParser

using MLStyle
using ...ADTs.RelationTerm
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.WiringDiagrams.RelationDiagrams
using Base.Iterators
using Reexport

@reexport using PEG

# export macro
export @relation_str

# export the lexing rules
export ws, eq, lparen, rparen, comma, EOL, colon, ident

# export the UWD rules
export judgements, judgement, args, arg, outerPorts, context, statement, body, uwd, line

# ## Create some rules 
# These basic rules are for *lexing*, they define character classes that will help us
# break up text into words or other syntactic constructs. They should be reused between
# grammars as the lowest level of syntactic structure.

@rule ws = r"\s*"
@rule eq = r"="p
@rule lparen = r"\("
@rule rparen = r"\)"
@rule comma = r","p
@rule EOL = "\n" , r";"
@rule colon = r":"p
@rule ident = r"[^:{}→\n;=,\(\)\s]+"


# Now we get to the syntax structures specific to our DSL.
# A judgement is an of the form x:X. We need to handle the items in the middle of list and the last item separately.
# It would be nice to have a better way to do this, but basically anything that can occur in a list has two rules associated with it.
# We use the prefix `fin` for final.

@rule judgements = (judgement & (ws & comma & ws & judgement)[*])[:?] |> v -> collect(v)
@rule judgement = ident & colon & ident |> v -> Typed(Symbol(v[1]), Symbol(v[3])),
      ident |> v -> Untyped(Symbol(v))

# A context is a list of judgements between brackets. When a rule ends with `|> f`
# it means to call `f` on the result of the parser inside the recursion.
# We are using these functions to get more structured output as we pop the function call stack.
# we don't want to end up with an `Array{Any}` that is deeply nested as the return value of our parse.

@rule outerPorts = lparen & ws & args & ws & rparen |> v->v[3]
@rule context = lparen & ws & judgements & ws & rparen |> v->v[3]

# Our statements are of the form `R(a,b,c)`. A name(list of names).
@rule statement = ident & lparen & ws & args & ws & rparen |> v -> Statement(Symbol(v[1]), v[4])

# We have a list of arguments separated by commas.
# An argument is a port that may or may not hold a name.
@rule args = (arg & (ws & comma & ws & arg)[*])[:?]  |> v -> collect(v)
@rule arg = ident & eq & ident |> v -> Kwarg(Symbol(v[1]), Untyped(Symbol(v[3]))),
  ident |> v -> Untyped(Symbol(v))

# A line is statement, with some whitespace ended by a EOL character.
# The body of our relational program is a list of lines between braces.
@rule line = ws & statement & r"[^\S\r\n]*" & EOL |> v->v[2]
@rule body = r"{\s*"p & line[*] & r"\n?}"p |> v->v[2]

# The UWD is a body and then a context for it separated by the word "where".

@rule uwd = outerPorts & ws & "where" & ws & context & ws & body |> v -> buildUWDExpr(v)

# Some of our rules construct higher level structures for the results. Those methods are defined here:

# Collects and flattens arguments into a single list
collect(v::Vector{Any}) = begin
  if isempty(v)
    return []
  else
    args = v[1]
    output = (last.(args[2]))
    pushfirst!(output, first(args))
  end
end

buildUWDExpr(v::Vector{Any}) = begin
  # Build a dictionary from our context for typing
  context_dict = Dict(judgement.var => judgement for judgement in v[5])

  # Perform Type Checking for Outer Ports
  for op in v[1]
    if op isa Kwarg
      if haskey(context_dict, op.var)
        op.var = context_dict[op.var]  # Overwrite the Untyped var with Typed
      end
    else # Regular Var Case
      if haskey(context_dict, op)
        op = context_dict[op]  # Overwrite the Untyped var with Typed    
      end
    end
  end
  
  # DEBUG
  println("Outer Ports: ", v[1])
  println("Context: ", v[5])

  # Perform Type Checking for Statements O(n) for n statement args
  for s in v[7]
    for i in 1:length(s.variables)
      var = s.variables[i]
      if haskey(context_dict, var.var)
        s.variables[i] = context_dict[var.var]  # Overwrite the Untyped var with Typed
      end
    end
    # Confirm Relation Vars are in Context
    isnothing(v[5]) || s.variables ⊆ v[5] ||
      error("One of variables $(s.variables) is not declared in context $(v[5])")
  end

  # Confirm Outer Vars are in Context
  isnothing(v[5]) || v[1] ⊆ v[5] ||
    error("One of variables $(v[1]) is not declared in context $(v[5])")
  
  # Construct Expression
  UWDExpr(v[1], v[5], v[7])
end

#  macro that parses and constructs UWD diagram from relationalProgram syntax.
macro relation_str(x::String) begin
  uwd_exp = parse_whole(uwd, x) end
  return RelationTerm.construct(RelationDiagram, parse_whole(uwd, x))
end

end
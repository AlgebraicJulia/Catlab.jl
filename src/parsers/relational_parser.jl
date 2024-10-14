module Relational_Parser
using MLStyle
using SyntacticModels.ASKEMUWDs
using Base.Iterators
using Reexport

@reexport using PEG

# export macro
export @relation_str

# export the lexing rules
export ws, eq, lparen, rparen, comma, EOL, colon, elname, obname

# export the UWD rules
export finjudgement, judgement, context, statement, body, uwd, line

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
@rule elname = r"[^:{}→\n;=,\(\)\s]+"
@rule obname = r"[^:{}→\n;=,\(\)\s]+"


# Now we get to the syntax structures specific to our DSL.
# A judgement is an of the form x:X. We need to handle the items in the middle of list and the last item separately.
# It would be nice to have a better way to do this, but basically anything that can occur in a list has two rules associated with it.
# We use the prefix `fin` for final.

@rule judgement = elname & colon & obname & comma |> Typed
@rule finjudgement = elname & colon & obname |> Typed

# A context is a list of judgements between brackets. When a rule ends with `|> f`
# it means to call `f` on the result of the parser inside the recursion.
# We are using these functions to get more structured output as we pop the function call stack.
# we don't want to end up with an `Array{Any}` that is deeply nested as the return value of our parse.

@rule context = r"{"p & judgement[*] & finjudgement & ws & r"}"p |> buildcontext

# Our statements are of the form `R(a,b,c)`. A name(list of names).
@rule statement = elname & lparen & ws & arg[*] & finarg & ws & rparen |> Statement
@rule arg = elname & comma
@rule finarg = elname

# A line is statement, with some whitespace ended by a EOL character.
# The body of our relational program is a list of lines between braces.

@rule line = ws & statement & r"[^\S\r\n]*" & EOL |> v->v[2]
@rule body = r"{\s*"p & line[*] & r"\n?}"p |> v->v[2]

# The UWD is a body and then a context for it separated by the word "where".

@rule uwd = body & ws & "where" & ws & context |> v -> buildUWDExpr(v)

# Some of our rules construct higher level structures for the results. Those methods are defined here:

ASKEMUWDs.Typed(j::Vector{Any}) = begin
  Typed(Symbol(j[1]), Symbol(j[3]))
end

buildcontext(v::Vector{Any}) = begin
  push!(v[2], v[3])
  return v[2]
end

ASKEMUWDs.Statement(v::Vector{Any}) = begin
  args = (Untyped∘Symbol∘first).(v[4])
  push!(args, Untyped(Symbol(v[5])))
  Statement(Symbol(v[1]), args)
end

buildUWDExpr(v::Vector{Any}) = begin
  # Extract Outerports from context:
  outer_ports = [first(v[5]), last(v[5])]

  # Build a dictionary from our list for cheaper lookups O(n) for n judgements
  context_dict = Dict(judgement.var => judgement for judgement in v[5])

  # Perform Type Checking for Statements O(m) for m statement args
  for s in v[1]
    for i in 1:length(s.variables)
      var = s.variables[i]
      if haskey(context_dict, var.var)
        s.variables[i] = context_dict[var.var]  # Overwrite the Untyped var with Typed
      end
    end
  end

  # Total Complexity: O(n) where m = n + constant intersections.
  # O(m) + O(n) = O(n + constant) + O(n) = O(n) + O(n) = O(n)

  # Construct Expression
  UWDExpr(outer_ports, v[1])
end

#  macro that parses and constructs UWD diagram from relationalProgram syntax.
macro relation_str(x::String) begin
  uwd_exp = parse_whole(uwd, x) end
  return ASKEMUWDs.construct(RelationDiagram, parse_whole(uwd, x))
end

end
"""    RelationalParser

Parses string input into a `RelationDiagram` via a string macro combined with a parsing expression grammar
that generates an ADT representation of an UWD to be constructed into an ACSet.
"""
module RelationalParser

using MLStyle
using Base.Iterators
using Reexport
using ...ADTs.RelationTerm
using ...WiringDiagrams.UndirectedWiringDiagrams
using ...WiringDiagrams.RelationDiagrams
using ..ParserCore: ws, eq, lparen, rparen, comma, EOL, colon, ident, expr, collect


@reexport using PEG

export @relation_str

# export the UWD rules
export judgements, judgement, args, arg, outerPorts, context, statement, body, uwd, line


# UWD Parsing Expression Grammar
################################

# A UWD consists of a list of outer ports, a context, and a body.
@rule uwd = outerPorts & ws & "where" & ws & context & ws & body |> v -> buildUWDExpr(v)

# Outer ports are a list of arguments enclosed in parenthesis.
# Context is a list of judgements enclosed in parenthesis.
@rule outerPorts = lparen & ws & args & ws & rparen |> v->v[3]
@rule context = lparen & ws & judgements & ws & rparen |> v->v[3]

# Judgements consists of a list of judgements separated by commas. There can be 0 or more judgements.
# A typed judgement is of the form (x:X) while an untyped judgement is of the form (x).
# A type is an expression as we want to allow for complex types.
@rule judgements = (judgement & (ws & comma & ws & judgement)[*])[:?] |> v -> collect(v)
@rule judgement = ident & colon & expr |> v -> Typed(Symbol(v[1]), v[3]),
      ident |> v -> Untyped(Symbol(v))

# A body is a list of lines between braces.
# Each line holds a statement/relation.
@rule body = r"{\s*"p & line[*] & r"\n?}"p |> v->v[2]
@rule line = ws & statement & r"[^\S\r\n]*" & EOL |> v->v[2]

# Our statements are of the form `R(a,b,c)`. A name(list of names).
@rule statement = ident & lparen & ws & args & ws & rparen |> v -> Statement(Symbol(v[1]), v[4])

# Arguments consists of a list of arguments separated by commas. There can be 0 or more arguments.
# An argument is a var that may be a keyword argument.
@rule args = (arg & (ws & comma & ws & arg)[*])[:?]  |> v -> collect(v)
@rule arg = ident & eq & ident |> v -> Kwarg(Symbol(v[1]), Untyped(Symbol(v[3]))),
  ident |> v -> Untyped(Symbol(v))


# Semantic Analysis
####################

buildUWDExpr(v::Vector{Any}) = begin
  # Build a dictionary from our context for easy lookup when type checking.
  context_dict = Dict(judgement.var => judgement for judgement in v[5])
  
  # Perform Type Checking for Outer Ports
  outer_ports = Vector{Var}(v[1])

  for i in eachindex(outer_ports)
    if outer_ports[i] isa Kwarg #Kwarg Case
      if haskey(context_dict, outer_ports[i].var.var)
        outer_ports[i] = Kwarg(outer_ports[i].name, context_dict[outer_ports[i].var.var])  # Overwrite the Untyped var with Typed if it typed in context
      else
        isempty(v[5]) ||
        error("Variable $(outer_ports[i].name) is not declared in context $(v[5])")
      end
    else # Regular Var Case
      if haskey(context_dict, outer_ports[i].var)
        outer_ports[i] = context_dict[outer_ports[i].var]  # Overwrite the Untyped var with Typed if it typed in context 
      else
        isempty(v[5]) ||
        error("Variable $(outer_ports[i]) is not declared in context $(v[5])")
      end
    end
  end

  # Perform Type Checking for each statement
  for s in v[7]
    for i in 1:length(s.variables)
      var = s.variables[i]
      if var isa Kwarg # Kwarg Case
        if haskey(context_dict, var.var.var)
          s.variables[i] = Kwarg(var.name, context_dict[var.var.var])  # Overwrite the Untyped var with Typed if it typed in context
        else
          isempty(v[5]) ||
          error("Variable $(var.name) is not declared in context $(v[5])")
        end 
      else # Regular Var Case
        if haskey(context_dict, var.var)
          s.variables[i] = context_dict[var.var]  # Overwrite the Untyped var with Typed if it typed in context
        else
          isempty(v[5]) ||
          error("Variable $(var) is not declared in context $(v[5])")
        end
      end
    end    
  end

  # Construct Expression
  UWDExpr(outer_ports, v[5], v[7])
end

# Macro that parses and constructs UWD diagram from relationalProgram syntax.
macro relation_str(x::String) begin
  uwd_exp = parse_whole(uwd, x) end
  return RelationTerm.construct(RelationDiagram, parse_whole(uwd, x))
end

end
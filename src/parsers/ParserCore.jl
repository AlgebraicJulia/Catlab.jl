""" Core components of a Parsing Expression Grammar
"""
module ParserCore

using Reexport
@reexport using PEG

""" Lexical Analysis Rules

These basic rules are for *lexing*, they define character classes that will help us break up text into words or other syntactic constructs.
They should be reused between grammars as the lowest level of syntactic structure
"""
# Exports Generic Lexical Rules
export ws, eq, lparen, rparen, comma, EOL, colon, ident

# Defines Generic Lexical Rules
@rule ws = r"\s*"
@rule eq = r"="p
@rule lparen = r"\("
@rule rparen = r"\)"
@rule comma = r","p
@rule EOL = "\n" , r";"
@rule colon = r":"p
@rule ident = r"[^:{}→\n;=,\(\)\s]+"

""" Syntactical Analysis Rules

These basic rules are for *Parsing*, they define rules for how to combine lexed tokens into more complex structures. Furthermore, they ensure
basic grammatical rules are followed.
"""
# Exports Generic Syntactical Rules
export expr

# Exports Generic Syntactical Helper Functions
export parse_identifier, collect

# Defines Generic Syntactical Rules

# Rules for parsing Julia Expressions
@rule expr = ident & lparen & ws & expr_args & ws & rparen |> v -> Expr(Symbol(v[1]), v[4]...),
  ident |> v -> parse_identifier(v)
@rule expr_args = (expr & (ws & comma & ws & expr)[*])[:?] |> v -> collect(v)

# Syntactical Helper Functions
##############################

# Parses ident as a symbol or integer
function parse_identifier(v)
  v_parsed = tryparse(Int, v)
  if isnothing(v_parsed)
    Symbol(v)
  else
    v_parsed
  end
end

# Collects/Flattens arguments of format "(arg & (ws & comma & ws & arg)[*])[:?]" Only
# Supports Lists such as "()" and "(a)" and "(a,b,c)"
function collect(v::Vector{Any})
  if isempty(v)
    return []
  else
    args = v[1]
    output = (last.(args[2]))
    pushfirst!(output, first(args))
  end
end

end
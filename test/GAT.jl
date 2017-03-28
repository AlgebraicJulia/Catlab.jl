import CompCat: GAT
using CompCat.GAT

using Base.Test
import DataStructures: OrderedDict

# Julia expression parsing
##########################

raw_expr(name, args...) = GAT.RawExpr(
  name, [ isa(x,Symbol) ? raw_expr(x) : x for x in args ])

# Raw expressions
@test GAT.parse_raw_expr(:(Ob)) == raw_expr(:Ob)
@test GAT.parse_raw_expr(:(Hom(X,Y))) == raw_expr(:Hom, :X, :Y)
@test_throws ParseError GAT.parse_raw_expr(:("Ob"))
@test_throws ParseError GAT.parse_raw_expr(:(Hom(X,0)))

# Contexts
@test (GAT.parse_context(:((X::Ob, Y::Ob))) == 
       GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob))))
@test (GAT.parse_context(:((X::Ob, Y::Ob, f::Hom(X,Y)))) == 
       GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob), 
                    :f => raw_expr(:Hom, :X, :Y))))
@test GAT.parse_context(:(())) == GAT.Context()
@test_throws ParseError GAT.parse_context(:((X::Ob, X::Ob))) # Repeat variables

# Type constructor
expr = :(Ob::TYPE)
cons = GAT.TypeConstructor(:Ob, [], GAT.Context())
@test GAT.parse_constructor(expr) == cons

expr = :(Hom(X,Y)::TYPE <= (X::Ob, Y::Ob))
context = GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob)))
cons = GAT.TypeConstructor(:Hom, [:X,:Y], context)
@test GAT.parse_constructor(expr) == cons

# Term constructor
expr = :(unit()::Ob)
cons = GAT.TermConstructor(:unit, [], raw_expr(:Ob), GAT.Context())
@test GAT.parse_constructor(expr) == cons

expr = :(id(X)::Hom(X,X) <= (X::Ob,))
context = GAT.Context(:X => raw_expr(:Ob))
cons = GAT.TermConstructor(:id, [:X], raw_expr(:Hom,:X,:X), context)
@test GAT.parse_constructor(expr) == cons

expr = :(compose(f,g)::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z)))
context = GAT.Context((
  :X => raw_expr(:Ob), :Y => raw_expr(:Ob), :Z => raw_expr(:Ob),
  :f => raw_expr(:Hom,:X,:Y), :g => raw_expr(:Hom,:Y,:Z)))
cons = GAT.TermConstructor(:compose, [:f,:g], raw_expr(:Hom,:X,:Z), context)
@test GAT.parse_constructor(expr) == cons

# Julia functions
parse_fun = (expr) -> GAT.parse_function(GAT.filter_line(expr, recurse=true))
@test (parse_fun(:(function f(x,y) x end)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test (parse_fun(:(function f(x::Int,y::Int)::Int x end)) == 
       GAT.JuliaFunction(:(f(x::Int,y::Int)), :Int, quote x end))
@test (parse_fun(:(f(x,y) = x)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test_throws ParseError parse_fun(:(f(x,y)))

# Macros
########

# Signature of the theory of categories
@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom, codom)::TYPE <= (dom::Ob, codom::Ob)
  
  id(X)::Hom(X,X) <= (X::Ob,)
  compose(f,g)::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z))
end

# Manually constructed signature of theory of categories
head = GAT.SignatureBinding(:Category, [:Ob, :Hom])
types = OrderedDict((
  :Ob => GAT.TypeConstructor(:Ob, [], GAT.Context()),
  :Hom => GAT.TypeConstructor(:Hom, [:dom,:codom], 
    GAT.Context((:dom => raw_expr(:Ob), :codom => raw_expr(:Ob)))),
))
terms = OrderedDict((
  :id => GAT.TermConstructor(:id, [:X], raw_expr(:Hom,:X,:X), 
    GAT.Context(:X => raw_expr(:Ob))),
  :compose => GAT.TermConstructor(:compose, [:f,:g], raw_expr(:Hom,:X,:Z),
    GAT.Context((
      :X => raw_expr(:Ob), :Y => raw_expr(:Ob), :Z => raw_expr(:Ob),
      :f => raw_expr(:Hom,:X,:Y), :g => raw_expr(:Hom,:Y,:Z)))),
))
category_signature = GAT.Signature(head, types, terms)

@test Category.signature == category_signature

# Equivalent shorthand definition of Category signature
# @signature CategoryAbbrev(Ob,Hom) begin
#   Ob::TYPE
#   Hom(dom::Ob, codom::Ob)::TYPE
#   
#   id(X::Ob)::Hom(X,X)
#   compose(f::Hom(A,B),g::Hom(B,C))::Hom(A,C) <= begin
#     A::Ob
#     B::Ob
#     C::Ob
#   end
# end

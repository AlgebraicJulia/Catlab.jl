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
expr = quote
  X::Ob
  Y::Ob
end
context = GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob)))
@test GAT.parse_context(expr) == context

expr = quote
  X::Ob
  Y::Ob
  f::Hom(X,Y)
end
context = GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob), 
                       :f => raw_expr(:Hom, :X, :Y)))
@test GAT.parse_context(expr) == context

expr = quote end
@test GAT.parse_context(expr) == GAT.Context()

expr = quote
  X::Ob
  X::Ob
end
@test_throws ParseError GAT.parse_context(expr) # Repeat variables

# Type constructor
expr = :(type Ob end)
cons = GAT.TypeConstructor(:Ob, [], GAT.Context())
@test GAT.parse_type_constructor(expr) == cons

expr = :(type Hom(X,Y)
  X::Ob
  Y::Ob
end)
context = GAT.Context((:X => raw_expr(:Ob), :Y => raw_expr(:Ob)))
cons = GAT.TypeConstructor(:Hom, [:X,:Y], context)
@test GAT.parse_type_constructor(expr) == cons

# Term constructor
expr = :(function unit()::Ob end)
cons = GAT.TermConstructor(:unit, [], raw_expr(:Ob), GAT.Context())
@test GAT.parse_term_constructor(expr) == cons

expr = :(function id(X)::Hom(X,X)
  X::Ob
end)
context = GAT.Context(:X => raw_expr(:Ob))
cons = GAT.TermConstructor(:id, [:X], raw_expr(:Hom,:X,:X), context)
@test GAT.parse_term_constructor(expr) == cons

expr = :(function compose(f,g)::Hom(X,Z)
  X::Ob
  Y::Ob
  Z::Ob
  f::Hom(X,Y)
  g::Hom(Y,Z)
end)
context = GAT.Context((
  :X => raw_expr(:Ob), :Y => raw_expr(:Ob), :Z => raw_expr(:Ob),
  :f => raw_expr(:Hom,:X,:Y), :g => raw_expr(:Hom,:Y,:Z)))
cons = GAT.TermConstructor(:compose, [:f,:g], raw_expr(:Hom,:X,:Z), context)
@test GAT.parse_term_constructor(expr) == cons

# Macros
########

# Signature of the theory of categories
@signature Category(Ob,Hom) begin
  type Ob end
  type Hom(dom, codom)
    dom::Ob
    codom::Ob
  end
  
  function id(X)::Hom(X,X)
    X::Ob
  end
  function compose(f,g)::Hom(X,Z)
    X::Ob
    Y::Ob
    Z::Ob
    f::Hom(X,Y)
    g::Hom(Y,Z)
  end
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
sig = GAT.Signature(head, types, terms)

@test Category == sig

# Equivalent shorthand definition of Category signature
# @signature CategoryAbbrev(Ob,Hom) begin
#   type Ob end
#   type Hom(dom::Ob, codom::Ob) end
#   
#   function id(A::Ob)::Hom(A,A) end
#   function compose(f::Hom(A,B),g::Hom(B,C))::Hom(A,C)
#     A,B,C::Ob
#   end
# end

# @signature MonoidalCatgory(Ob,Hom) extends Category(Ob,Hom) begin
#   function otimes(A,B)::Ob
#     A,B::Ob
#   end
#   function otimes(f,g)::Hom(otimes(A,C),otimes(B,D))
#     A,B,C,D::Ob
#     f::Hom(A,B)
#     g::Hom(C,D)
#   end
#   function munit()::Ob end
# end

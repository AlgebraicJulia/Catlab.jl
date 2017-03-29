import CompCat: GAT
using CompCat.GAT

using Base.Test
import DataStructures: OrderedDict

# Julia parsing
###############

# Functions
parse_fun = (expr) -> GAT.parse_function(GAT.filter_line(expr, recurse=true))
@test (parse_fun(:(function f(x,y) x end)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test (parse_fun(:(function f(x::Int,y::Int)::Int x end)) == 
       GAT.JuliaFunction(:(f(x::Int,y::Int)), :Int, quote x end))
@test (parse_fun(:(f(x,y) = x)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test_throws ParseError parse_fun(:(f(x,y)))

# GAT parsing
#############

# Raw expressions
@test GAT.parse_raw_expr(:(Ob)) == :Ob
@test GAT.parse_raw_expr(:(Hom(X,Y))) == :(Hom(X,Y))
@test_throws ParseError GAT.parse_raw_expr(:("Ob"))
@test_throws ParseError GAT.parse_raw_expr(:(Hom(X,0)))

# Contexts
@test (GAT.parse_context(:((X::Ob, Y::Ob))) == 
       GAT.Context((:X => :Ob, :Y => :Ob)))
@test (GAT.parse_context(:((X::Ob, Y::Ob, f::Hom(X,Y)))) == 
       GAT.Context((:X => :Ob, :Y => :Ob, :f => :(Hom(X,Y)))))
@test GAT.parse_context(:(())) == GAT.Context()
@test_throws ParseError GAT.parse_context(:((X::Ob, X::Ob))) # Repeat variables

# Type constructor
expr = :(Ob::TYPE)
cons = GAT.TypeConstructor(:Ob, [], GAT.Context())
@test GAT.parse_constructor(expr) == cons

expr = :(Hom(X,Y)::TYPE <= (X::Ob, Y::Ob))
context = GAT.Context((:X => :Ob, :Y => :Ob))
cons = GAT.TypeConstructor(:Hom, [:X,:Y], context)
@test GAT.parse_constructor(expr) == cons

# Term constructor
expr = :(unit()::Ob)
cons = GAT.TermConstructor(:unit, [], :Ob, GAT.Context())
@test GAT.parse_constructor(expr) == cons

cons = GAT.TermConstructor(:id, [:X], :(Hom(X,X)), GAT.Context(:X => :Ob))
@test GAT.parse_constructor(:(id(X)::Hom(X,X) <= (X::Ob,))) == cons
@test GAT.parse_constructor(:(id(X::Ob)::Hom(X,X))) == cons

expr = :(compose(f,g)::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z)))
context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
cons = GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)), context)
@test GAT.parse_constructor(expr) == cons
expr = :(compose(f::Hom(X,Y), g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob))
@test GAT.parse_constructor(expr) == cons

# Signatures
############

# Signature of the theory of categories
@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom, codom)::TYPE <= (dom::Ob, codom::Ob)
  
  id(X)::Hom(X,X) <= (X::Ob,)
  compose(f,g)::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z))
end

# Manually constructed signature of theory of categories
types = OrderedDict((
  :Ob => GAT.TypeConstructor(:Ob, [], GAT.Context()),
  :Hom => GAT.TypeConstructor(:Hom, [:dom,:codom], 
    GAT.Context((:dom => :Ob, :codom => :Ob))),
))
terms = OrderedDict((
  :id => GAT.TermConstructor(:id, [:X], :(Hom(X,X)), GAT.Context(:X => :Ob)),
  :compose => GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)),
    GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                 :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))),
))
category_signature = GAT.Signature(types, terms)

@test isa(Category, Module)
@test Category.signature() == category_signature

# Equivalent shorthand definition of Category signature
@signature CategoryAbbrev(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y),g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob)
end

@test CategoryAbbrev.signature() == category_signature

# Methods for signature
accessors = [ GAT.JuliaFunction(:(dom(::Hom)), :Ob),
              GAT.JuliaFunction(:(codom(::Hom)), :Ob) ]
constructors = [ GAT.JuliaFunction(:(id(X::Ob)), :Hom),
                 GAT.JuliaFunction(:(compose(f::Hom, g::Hom)), :Hom) ]
@test GAT.accessors(Category.signature()) == accessors
@test GAT.constructors(Category.signature()) == constructors
@test GAT.interface(Category) == [accessors; constructors]

# Utility functions
###################

@test GAT.strip_type(:Ob) == :Ob
@test GAT.strip_type(:(Hom(X,Y))) == :Hom
@test GAT.strip_type(:(Hom(dual(X),dual(Y)))) == :Hom

@test GAT.strip_types(:(id(X::Ob))) == :(id(X::Ob))
@test GAT.strip_types(:(id(X::Ob)::Hom(X,X))) == :(id(X::Ob)::Hom)
@test (GAT.strip_types(:(function id(X::Ob)::Hom(X,X) end)) ==
       :(function id(X::Ob)::Hom end))

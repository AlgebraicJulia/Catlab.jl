module TestGAT

using Base.Test
import DataStructures: OrderedDict

import CompCat: GAT
using CompCat.GAT
  
# Julia expressions
###################

# Function generation
strip_lines(expr) = GAT.strip_lines(expr, recurse=true)
@test (GAT.gen_function(GAT.JuliaFunction(:(f(x,y)))) ==
       strip_lines(:(function f(x,y) end)))
@test (GAT.gen_function(GAT.JuliaFunction(:(f(x::Int,y::Int)), :Int)) ==
       strip_lines(:(function f(x::Int,y::Int)::Int end)))
@test (GAT.gen_function(GAT.JuliaFunction(:(f(x)), :Bool, :(isnull(x)))) ==
       strip_lines(:(function f(x)::Bool isnull(x) end)))

# Function parsing
parse_fun(expr) = GAT.parse_function(strip_lines(expr))
@test (parse_fun(:(function f(x,y) x end)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test (parse_fun(:(function f(x::Int,y::Int)::Int x end)) == 
       GAT.JuliaFunction(:(f(x::Int,y::Int)), :Int, quote x end))
@test (parse_fun(:(f(x,y) = x)) == 
       GAT.JuliaFunction(:(f(x,y)), Nullable(), quote x end))
@test_throws ParseError parse_fun(:(f(x,y)))

sig = GAT.JuliaFunctionSig(:f, [:Int,:Int])
@test GAT.parse_function_sig(:(f(x::Int,y::Int))) == sig
@test GAT.parse_function_sig(:(f(::Int,::Int))) == sig
@test GAT.parse_function_sig(:(f(x,y))) == GAT.JuliaFunctionSig(:f, [:Any,:Any])

# Type transformations
bindings = Dict((:r => :R, :s => :S, :t => :T))
@test GAT.replace_symbols(bindings, :(foo(x::r,y::s)::t)) == :(foo(x::R,y::S)::T)
@test GAT.replace_symbols(bindings, :(foo(xs::Vararg{r}))) == :(foo(xs::Vararg{R}))

# GAT expressions
#################

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

# Type transformations
bindings = Dict((:Ob => :Obj, :Hom => :Mor))
cons = GAT.TypeConstructor(:Hom, [:X,:Y],
  GAT.Context((:X => :Ob, :Y => :Ob)))
target = GAT.TypeConstructor(:Mor, [:X,:Y],
  GAT.Context((:X => :Obj, :Y => :Obj)))
@test GAT.replace_types(bindings, cons) == target

cons = GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)), 
  GAT.Context((:X => :Obj, :Y => :Obj, :Z => :Obj,
               :f => :(Hom(X,Y)), :g => :(Hom(Y,Z)))))
target = GAT.TermConstructor(:compose, [:f,:g], :(Mor(X,Z)), 
  GAT.Context((:X => :Obj, :Y => :Obj, :Z => :Obj,
               :f => :(Mor(X,Y)), :g => :(Mor(Y,Z)))))
@test GAT.replace_types(bindings, cons) == target

@test GAT.strip_type(:Ob) == :Ob
@test GAT.strip_type(:(Hom(X,Y))) == :Hom
@test GAT.strip_type(:(Hom(dual(X),dual(Y)))) == :Hom

# Signatures
############

# Signature of the theory of categories
@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom, codom)::TYPE <= (dom::Ob, codom::Ob)
  
  id(X)::Hom(X,X) <= (X::Ob,)
  compose(f,g)::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z))
end

@test isa(Category, Module)
@test sort(names(Category)) == sort([:Category, :Ob, :Hom])
@test isa(Category.Ob, Type) && isa(Category.Hom, Type)
@test isa(dom, Function) && isa(codom, Function)
@test isa(id, Function) && isa(compose, Function)

export dom, codom, id, compose
@test length(methodswith(Category.Ob)) == 1 # id
@test length(methodswith(Category.Hom)) == 3 # compose, dom, codom

# Manually constructed signature of theory of categories
types = [
  GAT.TypeConstructor(:Ob, [], GAT.Context()),
  GAT.TypeConstructor(:Hom, [:dom,:codom], 
    GAT.Context((:dom => :Ob, :codom => :Ob))),
]
terms = [
  GAT.TermConstructor(:id, [:X], :(Hom(X,X)), GAT.Context(:X => :Ob)),
  GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)),
    GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                 :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))),
]
category_signature = GAT.Signature(types, terms)

@test Category.class().signature == category_signature

# Equivalent shorthand definition of Category signature
@signature CategoryAbbrev(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y),g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob)
end

@test CategoryAbbrev.class().signature == category_signature

# Methods for signature
accessors = [ GAT.JuliaFunction(:(dom(::Hom)), :Ob),
              GAT.JuliaFunction(:(codom(::Hom)), :Ob) ]
constructors = [ GAT.JuliaFunction(:(id(X::Ob)), :Hom),
                 GAT.JuliaFunction(:(compose(f::Hom, g::Hom)), :Hom) ]
@test GAT.accessors(Category.class().signature) == accessors
@test GAT.constructors(Category.class().signature) == constructors
@test GAT.interface(Category.class()) == [accessors; constructors]

# Signature extension
@signature Semigroup(S) begin
  S::TYPE
  times(x::S,y::S)::S
end

@signature Semigroup(M) => MonoidExt(M) begin
  munit()::M
end

@test isa(Semigroup, Module) && isa(MonoidExt, Module)
@test length(methods(times)) == 2 # Semigroup.S, MonoidExt.M
@test length(methods(munit)) == 1 # MonoidExt.M

signature = GAT.Signature(
  [ GAT.TypeConstructor(:M, [], GAT.Context()) ],
  [ GAT.TermConstructor(:times, [:x,:y], :M,
      GAT.Context((:x => :M, :y => :M))),
    GAT.TermConstructor(:munit, [], :M, GAT.Context()) ],
)
@test MonoidExt.class().signature == signature

# GAT expressions in a signature
################################

sig = Category.class().signature
context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
@test GAT.expand_in_context(:X, [:f,:g], context, sig) == :(dom(f))
@test (GAT.expand_in_context(:(Hom(X,Z)), [:f,:g], context, sig) ==
       :(Hom(dom(f),codom(g))))

context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob, :f => :(Hom(X,Y))))
@test_throws ErrorException GAT.expand_in_context(:W, [:f], context, sig)
@test_throws ErrorException GAT.expand_in_context(:Z, [:f], context, sig)

context = GAT.Context((:X => :Ob, :Y => :Ob, :f => :(Hom(X,Y))))
@test GAT.equations(context, sig) == [ :(dom(f)) => :X, :(codom(f)) => :Y ]
@test GAT.equations([:f], context, sig) == []

context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
@test (GAT.equations(context, sig) ==
       [ :(dom(f)) => :X, :(codom(f)) => :Y,
         :(dom(g)) => :Y, :(codom(g)) => :Z ])
@test GAT.equations([:f,:g], context, sig) == [ :(dom(g)) => :(codom(f)) ]

# Instances
###########

@instance Semigroup(Vector) begin
  times(x::Vector, y::Vector) = [x; y]
end

@test times([1,2],[3,4]) == [1,2,3,4]

@signature Monoid(M) begin
  M::TYPE
  munit()::M
  times(x::M,y::M)::M
  
  times(xs::Vararg{M}) = foldl(times, xs)
end

# Incomplete instance of Monoid
@test_throws ErrorException @instance Monoid(String) begin
  times(x::AbsStringtractString, y::String) = string(x,y)
end

# Complete instance of Monoid
@instance Monoid(String) begin
  munit(::Type{String}) = ""
  times(x::String, y::String) = string(x,y)
end

@test length(methods(munit)) == 3 # Monoid, MonoidExt, String
@test munit(String) == ""
@test times("a", "b") == "ab"
@test times("a", "b", "c") == "abc"

end

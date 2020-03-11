module TestGAT

using Base.Meta: ParseError
using Test
using DataStructures: OrderedDict

import Catlab: GAT
using Catlab.GAT

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

expr = (quote "Object" Ob::TYPE end).args[2]
cons = GAT.TypeConstructor(:Ob, [], GAT.Context(), "Object")
@test GAT.parse_constructor(expr) == cons

expr = :(Hom(X,Y)::TYPE ⊣ (X::Ob, Y::Ob))
context = GAT.Context((:X => :Ob, :Y => :Ob))
cons = GAT.TypeConstructor(:Hom, [:X,:Y], context)
@test GAT.parse_constructor(expr) == cons

# Term constructor
expr = :(unit()::Ob)
cons = GAT.TermConstructor(:unit, [], :Ob, GAT.Context())
@test GAT.parse_constructor(expr) == cons

expr = (quote "Monoidal unit" munit()::Ob end).args[2]
cons = GAT.TermConstructor(:munit, [], :Ob, GAT.Context(), "Monoidal unit")
@test GAT.parse_constructor(expr) == cons

cons = GAT.TermConstructor(:id, [:X], :(Hom(X,X)), GAT.Context(:X => :Ob))
@test GAT.parse_constructor(:(id(X)::Hom(X,X) ⊣ (X::Ob))) == cons
@test GAT.parse_constructor(:(id(X::Ob)::Hom(X,X))) == cons

expr = :(compose(f,g)::Hom(X,Z) ⊣ (X::Ob, Y::Ob, Z::Ob, f::Hom(X,Y), g::Hom(Y,Z)))
context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
cons = GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)), context)
@test GAT.parse_constructor(expr) == cons
expr = :(compose(f::Hom(X,Y), g::Hom(Y,Z))::Hom(X,Z) ⊣ (X::Ob, Y::Ob, Z::Ob))
@test GAT.parse_constructor(expr) == cons

# Type transformations
bindings = Dict((:Ob => :Obj, :Hom => :Mor))
cons = GAT.TypeConstructor(:Hom, [:X,:Y],
  GAT.Context((:X => :Ob, :Y => :Ob)))
target = GAT.TypeConstructor(:Mor, [:X,:Y],
  GAT.Context((:X => :Obj, :Y => :Obj)))
@test GAT.replace_types(bindings, cons) == target

cons = GAT.TermConstructor(:compose, [:f,:g], :(Hom(X,Z)),
  GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
               :f => :(Hom(X,Y)), :g => :(Hom(Y,Z)))))
target = GAT.TermConstructor(:compose, [:f,:g], :(Mor(X,Z)),
  GAT.Context((:X => :Obj, :Y => :Obj, :Z => :Obj,
               :f => :(Mor(X,Y)), :g => :(Mor(Y,Z)))))
@test GAT.replace_types(bindings, cons) == target

cons = GAT.AxiomConstructor(:(==), Meta.parse("compose(compose(f,g),Hom(C,D))"),
  Meta.parse("compose(f,compose(g,Hom(C,D)))"),
  GAT.Context((:A => :Ob, :B => :Ob, :C => :Ob, :D => :Ob,
               :f => :(Hom(A,B)), :g => :(Hom(B,C)))))
target = GAT.AxiomConstructor(:(==), Meta.parse("compose(compose(f,g),Mor(C,D))"),
  Meta.parse("compose(f,compose(g,Mor(C,D)))"),
  GAT.Context((:A => :Obj, :B => :Obj, :C => :Obj, :D => :Obj,
               :f => :(Mor(A,B)), :g => :(Mor(B,C)))))
@test GAT.replace_types(bindings, cons) == target

cons = Dict(:→ => :Hom)
target = Dict(:→ => :Mor)
@test GAT.replace_types(bindings, cons) == target

@test GAT.strip_type(:Ob) == :Ob
@test GAT.strip_type(:(Hom(X,Y))) == :Hom
@test GAT.strip_type(:(Hom(dual(X),dual(Y)))) == :Hom

# Theories
############

# This try-catch block is a necessary work around because of a current bug
# where test_throws doesn't catch errors thrown from inside of a macro
@test_throws ParseError try @eval @signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom, codom)::TYPE ⊣ (dom::Ob, codom::Ob)
  @op (→) := Hom

  id(X)::(X → X) ⊣ (X::Ob)
  compose(f,g)::(X → Z) ⊣ (X::Ob, Y::Ob, Z::Ob, f::(X → Y), g::(Y → Z))
  @op (⋅) := compose

  (f ⋅ g) ⋅ h == f ⋅ (g ⋅ h) ⊣ ( A::Ob, B::Ob, C::Ob, D::Ob,
                                f::(A → B), g::(B → C), h::(C → D))
  f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  id(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
end
catch err;
  throw(err.error)
end

""" Theory of the theory of categories
"""
@theory Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom, codom)::TYPE ⊣ (dom::Ob, codom::Ob)
  @op (→) := Hom

  id(X)::(X → X) ⊣ (X::Ob)
  compose(f,g)::(X → Z) ⊣ (X::Ob, Y::Ob, Z::Ob, f::(X → Y), g::(Y → Z))
  @op (⋅) := compose

  (f ⋅ g) ⋅ h == f ⋅ (g ⋅ h) ⊣ ( A::Ob, B::Ob, C::Ob, D::Ob,
                                f::(A → B), g::(B → C), h::(C → D))
  f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  id(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
end

@test isa(Category, Module)
@test occursin("theory of categories", string(Docs.doc(Category)))
@test sort(names(Category)) == sort([:Category, :Ob, :Hom])
@test isa(Category.Ob, Type) && isa(Category.Hom, Type)
@test isa(dom, Function) && isa(codom, Function)
@test isa(id, Function) && isa(compose, Function)

# Manually constructed theory of categories
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
axioms = [
  GAT.AxiomConstructor(:(==), Meta.parse("compose(compose(f,g),h)"),
    Meta.parse("compose(f,compose(g,h))"),
    GAT.Context((:A => :Ob, :B => :Ob, :C => :Ob, :D => :Ob,
                 :f => :(Hom(A,B)), :g => :(Hom(B,C)), :h => :(Hom(C,D))))),
  GAT.AxiomConstructor(:(==), Meta.parse("compose(f,id(B))"), :f,
    GAT.Context((:A => :Ob, :B => :Ob, :f => :(Hom(A,B))))),
  GAT.AxiomConstructor(:(==), Meta.parse("compose(id(A),f)"), :f,
    GAT.Context((:A => :Ob, :B => :Ob, :f => :(Hom(A,B))))),
]
aliases = Dict(:⋅ => :compose, :→ => :Hom)
category_theory = GAT.Theory(types, terms, axioms, aliases)

@test Category.class().theory == category_theory

""" Equivalent shorthand definition of Category theory
"""
@theory CategoryAbbrev(Ob,Hom) begin
  @op begin
    (→) := Hom
    (⋅) := compose
  end

  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE

  id(X::Ob)::(X → X)
  (compose(f::(X → Y),g::(Y → Z))::(X → Z)) where (X::Ob, Y::Ob, Z::Ob)

  (f ⋅ g) ⋅ h == f ⋅ (g ⋅ h) ⊣ ( A::Ob, B::Ob, C::Ob, D::Ob,
                                f::(A → B), g::(B → C), h::(C → D))
  f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  id(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
end

@test CategoryAbbrev.class().theory == category_theory

# Methods for theory
accessors = [ GAT.JuliaFunction(:(dom(::Hom)), :Ob),
              GAT.JuliaFunction(:(codom(::Hom)), :Ob) ]
constructors = [ GAT.JuliaFunction(:(id(X::Ob)), :Hom),
                 GAT.JuliaFunction(:(compose(f::Hom, g::Hom)), :Hom) ]
alias_functions = [
  GAT.JuliaFunction(:(⋅(f::Hom, g::Hom)), :Hom, :(compose(f, g))),
  GAT.JuliaFunction(:(→(dom::Ob, codom::Ob)), :Hom, :(Hom(dom, codom))),
]
@test GAT.accessors(Category.class().theory) == accessors
@test GAT.constructors(Category.class().theory) == constructors
@test GAT.alias_functions(Category.class().theory) == alias_functions
@test GAT.interface(Category.class()) ==
  [accessors; constructors; alias_functions]

# Theory extension
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

theory = GAT.Theory(
  [ GAT.TypeConstructor(:M, [], GAT.Context()) ],
  [ GAT.TermConstructor(:times, [:x,:y], :M,
      GAT.Context((:x => :M, :y => :M))),
    GAT.TermConstructor(:munit, [], :M, GAT.Context()) ],
  [],
  Dict{Symbol,Symbol}()
)

@test MonoidExt.class().theory == theory

# GAT expressions in a theory
################################

theory = Category.class().theory
context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
@test GAT.expand_in_context(:X, [:f,:g], context, theory) == :(dom(f))
@test (GAT.expand_in_context(:(Hom(X,Z)), [:f,:g], context, theory) ==
       :(Hom(dom(f),codom(g))))

context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob, :f => :(Hom(X,Y))))
@test_throws ErrorException GAT.expand_in_context(:W, [:f], context, theory)
@test_throws ErrorException GAT.expand_in_context(:Z, [:f], context, theory)

context = GAT.Context((:X => :Ob, :Y => :Ob, :f => :(Hom(X,Y))))
@test GAT.equations(context, theory) == [ :(dom(f)) => :X, :(codom(f)) => :Y ]
@test GAT.equations([:f], context, theory) == []

context = GAT.Context((:X => :Ob, :Y => :Ob, :Z => :Ob,
                       :f => :(Hom(X,Y)), :g => :(Hom(Y,Z))))
@test (GAT.equations(context, theory) ==
       [ :(dom(f)) => :X, :(codom(f)) => :Y,
         :(dom(g)) => :Y, :(codom(g)) => :Z ])
@test GAT.equations([:f,:g], context, theory) == [ :(dom(g)) => :(codom(f)) ]

# Instances
###########

""" Vectors as an instance of the theory of semigroups
"""
@instance Semigroup(Vector) begin
  times(x::Vector, y::Vector) = [x; y]
end

@test times([1,2],[3,4]) == [1,2,3,4]

@signature Monoid(M) begin
  M::TYPE
  munit()::M
  times(x::M,y::M)::M
end

# Incomplete instance of Monoid
# XXX: Cannot use `@test_warn` since generated code won't be at toplevel.
#@test_warn "not implemented" @instance Monoid(String) begin
#  times(x::AbsStringtractString, y::String) = string(x,y)
#end

# Complete instance of Monoid
@instance Monoid(String) begin
  munit(::Type{String}) = ""
  times(x::String, y::String) = string(x,y)
end

@test length(methods(munit)) == 3 # Monoid, MonoidExt, String
@test munit(String) == ""
@test times("a", "b") == "ab"

# Reflection
@test invoke_term(Monoid, (String,), :munit) == ""
@test invoke_term(Monoid, (String,), :times, "a", "b") == "ab"

end

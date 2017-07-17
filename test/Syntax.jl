""" Test the Syntax module.

The unit tests are sparse because many of the Doctrine tests are really just
tests of the Syntax module.
"""
module TestSyntax

using Base.Test
using Catlab

# Monoid
########

""" Signature of the theory of monoids.
"""
@signature Monoid(Elem) begin
  Elem::TYPE
  munit()::Elem
  mtimes(x::Elem,y::Elem)::Elem
end

""" Syntax for the theory of monoids.
"""
@syntax FreeMonoid Monoid

elem(mod::Module, args...) = elem(mod.Elem, args...)

@test isa(FreeMonoid, Module)
@test contains(string(Docs.doc(FreeMonoid)), "theory of monoids")
@test sort(names(FreeMonoid)) == sort([:FreeMonoid, :Elem])

x, y, z = elem(FreeMonoid,:x), elem(FreeMonoid,:y), elem(FreeMonoid,:z)
@test isa(mtimes(x,y), FreeMonoid.Elem)
@test isa(munit(FreeMonoid.Elem), FreeMonoid.Elem)
@test mtimes(mtimes(x,y),z) != mtimes(x,mtimes(y,z))

# Test equality
@test x == elem(FreeMonoid,:x)
@test x != y
@test elem(FreeMonoid,"X") == elem(FreeMonoid,"X")
@test elem(FreeMonoid,"X") != elem(FreeMonoid,"Y")

# Test hash
@test hash(x) == hash(x)
@test hash(x) != hash(y)
@test hash(mtimes(x,y)) == hash(mtimes(x,y))
@test hash(mtimes(x,y)) != hash(mtimes(x,z))

@syntax FreeMonoidAssoc Monoid begin
  mtimes(x::Elem, y::Elem) = associate(Super.mtimes(x,y))
end

x, y, z = [ elem(FreeMonoidAssoc,sym) for sym in [:x,:y,:z] ]
e = munit(FreeMonoidAssoc.Elem)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) != x && mtimes(x,e) != x

@syntax FreeMonoidAssocUnit Monoid begin
  mtimes(x::Elem, y::Elem) = associate_unit(Super.mtimes(x,y), munit)
end

x, y, z = [ elem(FreeMonoidAssocUnit,sym) for sym in [:x,:y,:z] ]
e = munit(FreeMonoidAssocUnit.Elem)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) == x && mtimes(x,e) == x

abstract type MonoidExpr{T} <: BaseExpr{T} end
@syntax FreeMonoidTyped(MonoidExpr) Monoid

x = elem(FreeMonoidTyped.Elem, :x)
@test issubtype(FreeMonoidTyped.Elem, MonoidExpr)
@test isa(x, FreeMonoidTyped.Elem) && isa(x, MonoidExpr)

@signature Monoid(Elem) => MonoidNumeric(Elem) begin
  elem_int(x::Int)::Elem
end
@syntax FreeMonoidNumeric MonoidNumeric

x = elem_int(FreeMonoidNumeric.Elem, 1)
@test isa(x, FreeMonoidNumeric.Elem)
@test first(x) == 1

""" A monoid with two distinguished elements.
"""
@signature Monoid(Elem) => MonoidTwo(Elem) begin
  one()::Elem
  two()::Elem
end
""" The free monoid on two generators.
"""
@syntax FreeMonoidTwo MonoidTwo begin
  elem(::Type{Elem}, value) = error("No extra generators allowed!")
end

x, y = one(FreeMonoidTwo.Elem), two(FreeMonoidTwo.Elem)
@test all(isa(expr, FreeMonoidTwo.Elem) for expr in [x, y, mtimes(x,y)])
@test_throws ErrorException elem(FreeMonoidTwo, :x)

# Category
##########

@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y), g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob)
  
  compose(fs::Vararg{Hom}) = foldl(compose, fs)
end

@syntax FreeCategory Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g))
end

@test isa(FreeCategory, Module)
@test sort(names(FreeCategory)) == sort([:FreeCategory, :Ob, :Hom])

X, Y, Z, W = [ ob(FreeCategory.Ob, sym) for sym in [:X, :Y, :Z, :W] ]
f, g, h = hom(:f, X, Y), hom(:g, Y, Z), hom(:h, Z, W)
@test isa(X, FreeCategory.Ob) && isa(f, FreeCategory.Hom)
@test_throws MethodError FreeCategory.hom(:f)
@test dom(f) == X
@test codom(f) == Y

@test isa(id(X), FreeCategory.Hom)
@test dom(id(X)) == X
@test codom(id(X)) == X

@test isa(compose(f,g), FreeCategory.Hom)
@test dom(compose(f,g)) == X
@test codom(compose(f,g)) == Z
@test isa(compose(f,f), FreeCategory.Hom) # Doesn't check domains.

@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(f,g,h) == compose(compose(f,g),h)
@test dom(compose(f,g,h)) == X
@test codom(compose(f,g,h)) == W

@syntax FreeCategoryStrict Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

X, Y = ob(FreeCategoryStrict.Ob, :X), ob(FreeCategoryStrict.Ob, :Y)
f, g = hom(:f, X, Y), hom(:g, Y, X)

@test isa(compose(f,g,f), FreeCategoryStrict.Hom)
@test_throws SyntaxDomainError compose(f,f)

# Functor
#########

@instance Monoid(String) begin
  munit(::Type{String}) = ""
  mtimes(x::String, y::String) = string(x,y)
end

x, y, z = elem(FreeMonoid,:x), elem(FreeMonoid,:y), elem(FreeMonoid,:z)
gens = Dict(x => "x", y => "y", z => "z")
types = Dict(:Elem => String)
@test functor(types, mtimes(x,mtimes(y,z)); generators=gens) == "xyz"
@test functor(types, mtimes(x,munit(FreeMonoid.Elem)); generators=gens) == "x"

gen_terms = Dict(:elem => (x) -> string(first(x)))
@test functor(types, mtimes(x,mtimes(y,z)); generator_terms=gen_terms) == "xyz"
@test functor(types, mtimes(x,munit(FreeMonoid.Elem)); generator_terms=gen_terms) == "x"

constructors = Dict(:elem => (typ,val) -> string(val))
@test functor(types, mtimes(x,mtimes(y,z)); constructors=constructors) == "xyz"
@test functor(types, mtimes(x,munit(FreeMonoid.Elem)); constructors=constructors) == "x"

end

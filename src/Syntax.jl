module Syntax

export Ob, Mor, AtomicOb, AtomicMor, CompositeMor, IdentityMor
export ob, mor, dom, codom, id, compose

import ..Doctrine
using Typeclass

# Expressions
#############

""" Base type for expressions in categorical languages.

We define Julia types for each "kind" or "metatype" in the language: currently
*object* and *morphism*, perhaps later *2-morphism*, *3-morphism*, etc. The
concrete types are structurally similar to the core type `Expr` in Julia.

**Design note**: An alternative approach would represent every kind with the
`Expr` type, using its `typ` field to distinguish objects and morphisms. I think
that would be a mistake. It would conflate the `Ob` and `Mor` type parameters in
the type classes. More fundamentally, it is always wrong to change the kind of
an expression at the syntactic level, e.g., any rewrite rule that transforms an
object expression to a morphism expression makes a category error. We should
enforce this constraint at the type level in Julia.

At the other extreme, we could create a concrete type for each syntactic element
(`GeneratorMor`, `IdMor`, `CompositeMor`, etc). This idea is better than the
last but leads to a large proliferation of types and makes it inconvenient to
write generic code operating on expressions as a homogeneous data structure
(analogous to S-expressions).
"""
abstract DoctrineExpr

immutable ObExpr <: DoctrineExpr
  head::Symbol
  args::Array
  ObExpr(head, args...) = new(head, [args...])
end

immutable MorExpr <: DoctrineExpr
  head::Symbol
  args::Array
  MorExpr(head, args...) = new(head, [args...])
end

# Category
##########

@instance! Doctrine.Category ObExpr MorExpr begin
  dom(f::MorExpr) = dom(f, Val{f.head})
  codom(f::MorExpr) = codom(f, Val{f.head})
  id(A::ObExpr) = MorExpr(:id, A)
  
  function compose(f::MorExpr, g::MorExpr)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    MorExpr(:compose, f, g)
  end
end

# Generators
ob(A::Symbol) = ObExpr(:gen, A)
mor(f::Symbol, dom::ObExpr, codom::ObExpr) = MorExpr(:gen, f, dom, codom)

dom(f::MorExpr, ::Type{Val{:gen}}) = f.args[2]
dom(f::MorExpr, ::Type{Val{:compose}}) = dom(first(f.args))
dom(f::MorExpr, ::Type{Val{:id}}) = f.args[1]

codom(f::MorExpr, ::Type{Val{:gen}}) = f.args[3]
codom(f::MorExpr, ::Type{Val{:compose}}) = codom(last(f.args))
codom(f::MorExpr, ::Type{Val{:id}}) = f.args[1]

# Monoidal category
###################

end

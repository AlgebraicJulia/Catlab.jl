module Syntax

export Ob, Mor, AtomicOb, AtomicMor, CompositeMor, IdentityMor
export ob, mor, dom, codom, id, compose

import ..Doctrine
using Typeclass

abstract Ob
abstract Mor

# Category
##########

function expr(head::Symbol, args::Array, typ::Type)::Expr
  ex = Expr(head, args...)
  ex.typ = typ
  return ex
end

# Generators
ob(A::Symbol) = expr(:gen, [A], Ob)
mor(f::Symbol, dom::Expr, codom::Expr) = expr(:gen, [f,dom,codom], Mor)

@instance! Doctrine.Category Expr Expr begin
  dom(f::Expr) = dom(f, Val{f.head})
  codom(f::Expr) = codom(f, Val{f.head})
  id(A::Expr) = expr(:id, [A], Ob)
  
  function compose(f::Expr, g::Expr)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    expr(:compose, [f,g], Mor)
  end
end

dom(f::Expr, ::Type{Val{:gen}}) = f.args[2]
dom(f::Expr, ::Type{Val{:compose}}) = dom(first(f.args))
dom(f::Expr, ::Type{Val{:id}}) = f.args[1]

codom(f::Expr, ::Type{Val{:gen}}) = f.args[3]
codom(f::Expr, ::Type{Val{:compose}}) = codom(last(f.args))
codom(f::Expr, ::Type{Val{:id}}) = f.args[1]

# Monoidal category
###################

end

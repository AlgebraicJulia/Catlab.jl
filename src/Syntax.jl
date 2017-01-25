module Syntax

export Ob, Mor, AtomicOb, AtomicMor, CompositeMor, IdentityMor
export ob, mor, dom, codom, id, compose

import ..Doctrine
using Match
using Typeclass

abstract Ob
abstract Mor

# Category
##########

immutable AtomicOb <: Ob
  name::Symbol
end

immutable AtomicMor <: Mor
  name::Symbol
  dom::Ob
  codom::Ob
end

immutable CompositeMor <: Mor
  mors::Array{Mor}
end

immutable IdentityMor <: Mor
  ob::Ob
end

# Constructors
ob(A::Symbol)::Ob = AtomicOb(A)
mor(f::Symbol, dom::Ob, codom::Ob)::Mor = AtomicMor(f, dom, codom)

# Category interface
dom(f::AtomicMor) = f.dom
dom(f::CompositeMor) = dom(first(f.mors))
dom(f::IdentityMor) = f.obj

codom(f::AtomicMor) = f.codom
codom(f::CompositeMor) = codom(last(f.mors))
codom(f::IdentityMor) = f.obj

@instance! Doctrine.Category Ob Mor begin
  dom(f::Mor) = dom(f)
  codom(f::Mor) = codom(f)
  id(A::Ob) = IdentityMor(A)
  
  function compose(f::Mor, g::Mor)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    mors(f) = isa(f, CompositeMor) ? f.mors : f
    @match (f, g) begin 
      (IdentityMor, _) => g
      (_, IdentityMor) => f
      _ => CompositeMor([mors(f) mors(g)])
    end
  end
end

# Monoidal category
###################

end

module FreeCategory
import Category
using Match

abstract Obj <: Category.Obj
abstract Mor <: Category.Mor

# Category
##########

type AtomicObj <: Obj
  name::Symbol
end

type AtomicMor <: Mor
  name::Symbol
  dom::Obj
  codom::Obj
end

type CompositeMor <: Mor
  mors::Array{Mor}
end

type IdentityMor <: Mor
  obj::Obj
end

# Constructors
obj(A::Symbol)::Obj = AtomicObj(A)
mor(f::Symbol, dom::Obj, codom::Obj)::Mor = AtomicMor(f, dom, codom)

# Category interface
dom(f::AtomicMor) = f.dom
dom(f::CompositeMor) = dom(first(f.mors))
dom(f::IdentityMor) = f.obj

codom(f::AtomicMor) = f.codom
codom(f::CompositeMor) = codom(last(f.mors))
codom(f::IdentityMor) = f.obj

id(A::AtomicObj)::Mor = IdentityMor(A)

function compose(f::Mor, g::Mor)::Mor
  if codom(f) != dom(g)
    error("Incompatible domains")
  end
  mors(f) = @match f begin
    CompositeMor(fs) => fs
    _ => f
  end
  CompositeMor([mors(f) mors(g)])
end

# Monoidal category
###################

end

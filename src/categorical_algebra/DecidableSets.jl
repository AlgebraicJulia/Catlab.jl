module DecidableSets
export DecidableSet,DecidableHom

import FunctionWrappers
import FunctionWrappers: FunctionWrapper
using Catlab.GAT
using Catlab.Theories
import Catlab.Theories: id, compose

struct DecidableSet{T}
  decider::FunctionWrapper{Bool,Tuple{T}}
  DecidableSet(T::DataType,f::Function) = new{T}(FunctionWrapper{Bool,Tuple{T}}(f))
end

function (t::DecidableSet{T})(x::T)::Bool where {T}
  t.decider(x)
end

basetype(t::DecidableSet{T}) where {T} = T

struct DecidableHom{T,S}
  dom::DecidableSet{T}
  codom::DecidableSet{S}
  f::FunctionWrapper{S,Tuple{T}}
  DecidableHom(dom::DecidableSet{T},codom::DecidableSet{S},f) where {T,S} =
    new{T,S}(dom,codom,FunctionWrapper{S,Tuple{T}}(f))
end

function (f::DecidableHom{T,S})(x::T)::S where {T,S}
  @assert f.dom(x)
  y = f.f(x)
  @assert f.codom(y)
  y
end

function compose(f::DecidableHom{T,S},g::DecidableHom{S,U}) where {T,S,U}
  function h(x)
    y = f.f(x)
    @assert f.codom(y)
    @assert g.dom(y)
    g.f(y)
  end
  DecidableHom(f.dom,g.codom,h)
end

# This is really the category of decidable sets and partial functions...
@instance Category(DecidableSet, DecidableHom) begin
  dom(f::DecidableHom) = f.dom
  codom(f::DecidableHom) = f.codom

  id(t::DecidableSet) = DecidableHom(t,t,x->x)
  compose(f::DecidableHom,g::DecidableHom) = begin
    @assert basetype(f.codom) == basetype(g.dom)
    compose(f,g)
  end
end

end

module PredicatedSets
export PredicatedSet,PredicatedHom

import FunctionWrappers
import FunctionWrappers: FunctionWrapper
using ...GAT
using ...Theories
import ...Theories: id, compose

struct PredicatedSet{T}
  predicate::FunctionWrapper{Bool,Tuple{T}}
  PredicatedSet(T::DataType,f::Function) = new{T}(FunctionWrapper{Bool,Tuple{T}}(f))
end

function (t::PredicatedSet{T})(x::T)::Bool where {T}
  t.predicate(x)
end

basetype(t::PredicatedSet{T}) where {T} = T

struct PredicatedHom{T,S}
  dom::PredicatedSet{T}
  codom::PredicatedSet{S}
  f::FunctionWrapper{S,Tuple{T}}
  PredicatedHom(dom::PredicatedSet{T},codom::PredicatedSet{S},f) where {T,S} =
    new{T,S}(dom,codom,FunctionWrapper{S,Tuple{T}}(f))
end

function (f::PredicatedHom{T,S})(x::T)::S where {T,S}
  @assert f.dom(x)
  y = f.f(x)
  @assert f.codom(y)
  y
end

function compose(f::PredicatedHom{T,S},g::PredicatedHom{S,U}) where {T,S,U}
  function h(x)
    y = f.f(x)
    @assert f.codom(y)
    @assert g.dom(y)
    g.f(y)
  end
  PredicatedHom(f.dom,g.codom,h)
end

# This is really the category of decidable sets and partial functions...
@instance Category{PredicatedSet, PredicatedHom} begin
  dom(f::PredicatedHom) = f.dom
  codom(f::PredicatedHom) = f.codom

  id(t::PredicatedSet) = PredicatedHom(t,t,x->x)
  compose(f::PredicatedHom,g::PredicatedHom) = begin
    @assert basetype(f.codom) == basetype(g.dom)
    compose(f,g)
  end
end

end

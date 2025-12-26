module Setup
export BW, is_mat, is_normal

using AlgebraicRewriting
using Catlab, Catlab.CategoricalAlgebra, Catlab.Present, Catlab.Theories, Catlab.Graphs

using Catlab.Meta: Expr0

import Base: (*)

@present TheoryWeightedLabeledGraphCospan <: SchGraph begin
  (Weight, Color)::AttrType
  weight::Attr(E,Weight)
  color::Attr(V,Color)
  (I,O)::Ob
  i::Hom(I, V)
  o::Hom(O, V)
  # Not enforced, but:
  # i ⋅ color == false
  # o ⋅ color == true
end

@abstract_acset_type AbstractWeightedLabeledGraphCospan <: AbstractGraph

@acset_type WeightedLabeledGraphCospan(
  TheoryWeightedLabeledGraphCospan, index=[:src,:tgt,]
  ) <: AbstractWeightedLabeledGraphCospan

const BW = WeightedLabeledGraphCospan{Union{Expr0, Var, Int, Rational},
                                      Union{Expr0, Var, Bool}}

function BW(s,t,color=false,weight=1;i=[],o=[])
  i = i isa AbstractVector ? i : [i]
  o = o isa AbstractVector ? o : [o]
  color = color isa AbstractVector ? color : repeat([color], max(vcat(s,t)))
  weight = weight isa AbstractVector ? weight : repeat([weight], length(s))
  @acset BW begin
      V = length(color); E=length(s); I=length(i); O=length(o);
      i=i; o=o; color=color; weight=weight; src=s; tgt=t
  end
end

function (*)(g::BW, scalar::Union{Int,Rational})
  g = deepcopy(g)
  set_subpart!(g, :weight, [a*scalar for a in g[:weight]])
  return g
end

(*)(scalar::Union{Int,Rational}, g::BW) = g * scalar


function is_normal(g::BW)::Bool
  for v in vertices(g)
    if g[v, :color] # white node
      if !isempty(incident(g, v, :src)) return false end
    else
      if !isempty(incident(g, v, :tgt)) return false end
    end
  end
  st = collect(zip(g[:src], g[:tgt])) # at most one edge btw two nodes
  return length(st) == length(unique(st))
end

is_mat(g::BW) = (is_normal(g)
    && sort(g[:i]) == findall((!).(g[:color]))
    && sort(g[:o]) == findall(g[:color]))

end # module

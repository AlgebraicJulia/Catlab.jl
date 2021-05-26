module CospanRewrite
export OpenRule, open_pushout_complement, apply_open_rewrite, force

using AutoHashEquals

using ..StructuredCospans
using ..DPO
using ..Limits
using ..CSets
using ..FreeDiagrams
using ...Graphs
using ...Theories
using ...GAT
import ...Theories: id, compose, composeH, composeV, id2, idH, idV, id2H, id2V
import ..CSets: force
const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V);

"""
Rewrite rule for structured cospans

Left and right are intended to be discrete isomorphisms
"""
@auto_hash_equals struct OpenRule
    top::OpenGraph
    middle::OpenGraph
    bottom::OpenGraph
    left::Span
    center::Span # of Graph Transformations
    right::Span

    # Validate
    function OpenRule(top::OpenGraph,
                      mid::OpenGraph,
                      bot::OpenGraph,
                      lft::Span,
                      cent::Span,
                      rght::Span)

        is_discrete = leg -> (nparts(dom(leg),:E)
                            + nparts(codom(leg),:E) == 0)

        is_iso = leg ->let f=collect(leg[:V]), n=length(f);
                          (n == length(Set(f))
                          && n == codom(leg[:V]).set) end

        is_discrete_isospan = spn -> all(
            leg -> is_iso(leg) && is_discrete(leg), spn)

        @assert is_discrete_isospan(lft)
        @assert is_discrete_isospan(rght)

        #check commutivity
        for (quad, a,b,c,d) in [
            ("↑ ←", left(lft),   left(top),  left(mid),  left(cent)),
            ("↓ ←", right(lft),  left(bot),  left(mid),  right(cent)),
            ("↑ →", left(rght),  right(top), right(mid), left(cent)),
            ("↓ →", right(rght), right(bot), right(mid), right(cent))]
            err = "$quad $((a ⋅ b)[:V])!=$((c ⋅ d)[:V])"
            @assert collect((a ⋅ b)[:V]) == collect((c ⋅ d)[:V]) err
        end
        return new(top, mid, bot, lft, cent, rght)
    end
end

function force(s::Span)::Span
  return Span(map(force, s)...)
end

function force(r::OpenRule)::OpenRule
  return OpenRule(force(r.top), force(r.middle), force(r.bottom),
                  force(r.left), force(r.center), force(r.right))
end

"""
Based on figure at top of pg 15 of Cicala paper. Ignore "L" and
replace primes with 0, 1, 2 (1 for center / no prime, 0 for
top / prime, 2 for bottom / double prime)
Underscores indicate morphisms

Each OpenRule has 12 morphisms.
We need 9 pushouts and 3 pushout complements
"""
function open_pushout_complement(
    rule::OpenRule,
    target::OpenGraph,
    x0_y0::CSetTransformation, # match
    a0_c0::CSetTransformation, # match
    b0_d0::CSetTransformation  # match
    )::OpenRule

    # unpack input data
    c0_y0, d0_y0 = left(target),      right(target);
    a0_x0, b0_x0 = left(rule.top),    right(rule.top);
    a1_x1, b1_x1 = left(rule.middle), right(rule.middle);
    a2_x2, b2_x2 = left(rule.bottom), right(rule.bottom);
    a1_a0, a1_a2 = left(rule.left),   right(rule.left);
    b1_b0, b1_b2 = left(rule.right),  right(rule.right);
    x1_x0, x1_x2 = left(rule.center), right(rule.center);

    # compute results w/ DPO
    @assert valid_dpo(b1_b0, b0_d0)
    b1_d1, d1_d0 = pushout_complement(b1_b0, b0_d0);
    d1_d2, b2_d2 = pushout(b1_d1, b1_b2);
    _,     d2_y2 = pushout(b2_x2, b2_d2);
    _,     d0_y0 = pushout(b0_x0, b0_d0);
    _,     d1_y1 = pushout(b1_x1, b1_d1);

    @assert valid_dpo(x1_x0, x0_y0)
    x1_y1, y1_y0 = pushout_complement(x1_x0, x0_y0);
    y1_y2, _ = pushout(x1_y1, x1_x2);

    @assert valid_dpo(a1_a0, a0_c0)
    a1_c1, c1_c0 = pushout_complement(a1_a0, a0_c0);
    c1_c2, a2_c2 = pushout(a1_c1, a1_a2);
    _,     c2_y2 = pushout(a2_x2, a2_c2);
    _,     c0_y0 = pushout(a0_x0, a0_c0);
    _,     c1_y1 = pushout(a1_x1, a1_c1);

    # package up result
    top    = OpenGraph(apex(target), c0_y0[:V], d0_y0[:V]);
    middle = OpenGraph(codom(c1_y1), c1_y1[:V], d1_y1[:V]);
    bottom = OpenGraph(codom(c2_y2), c2_y2[:V], d2_y2[:V]);
    lft    = Span(c1_c0, c1_c2);
    center = Span(y1_y0, y1_y2);
    rght   = Span(d1_d0, d1_d2);
    return OpenRule(top, middle, bottom, lft, center, rght)
end

"""Generate derived rule and only keep the result open system"""
function apply_open_rewrite(
  rule::OpenRule,
  target::OpenGraph,
  x0_y0::CSetTransformation, # match
  a0_c0::CSetTransformation, # match
  b0_d0::CSetTransformation  # match
  )::OpenGraph
  res_rule = open_pushout_complement(rule,target,x0_y0,a0_c0,b0_d0)
  return res_rule.bottom
end

"""Compose spans via pullback"""
function composeSpan(f::Span{T}, g::Span{T})::Span{T} where {T}
    pbf, pbg = pullback(right(f), left(g))
    return Span(compose(pbf, left(f)), compose(pbg,right(g)))
  end

"""
Double category of structured cospan rewrite rules as described by
Daniel Cicala. Horizontal arrows are open systems, vertical arrows
are spans of discrete isomorphisms (we use discrete interfaces
between open systems)
"""
@instance DoubleCategory{Graph, Span, OpenGraph, OpenRule} begin
  @import dom, codom, top, bottom, left, right, ⋅
  idH(A::Graph) = let x=id(A)[:V]; OpenGraph(A, x, x) end
  idV(A::Graph) = Span(id(A), id(A))

  """Cospan composition given by pushout"""
  composeH(f::OpenGraph, g::OpenGraph)::OpenGraph = compose(f,g)

  """Span composition given by pullback"""
  composeV(f::Span, g::Span) = composeSpan(f, g)

  id2(A::Graph)::OpenRule = let h=idH(A), v=idV(A); OpenRule(h,h,h,v,v,v) end

  function id2H(f::Span)::OpenRule
    l, r   = f
    nd     = codom(l[:V]).set
    G      = Graph(nd)
    top    = idH(codom(l))
    middle = idH(G)
    bottom = idH(codom(r))
    up     = CSetTransformation(G, G, V=collect(l[:V]))
    down   = CSetTransformation(G, G, V=collect(r[:V]))
    return OpenRule(top, middle, bottom, f, Span(up, down), f)
  end

  function id2V(f::OpenGraph)::OpenRule
    l,c,r = dom(left(f)), apex(f), dom(right(f))
    lft   = let x=id(l); Span(x,x) end
    centr = let x=id(c); Span(x,x) end
    rght  = let x=id(r); Span(x,x) end
    return OpenRule(f, f, f, lft, centr, rght)
  end

  """    composeH(r₁, r₂)

  compose two rewrite rules horizontally as shown below:
      La → v ← Lα      Lα → p ← Lx     La→ v +(Lα) p ←Lx
      ↑    ↑    ↑      ↑    ↑    ↑     ↑     ↑         ↑
      Lb → w ← Lβ  ∘h  Lβ → q ← Ly  =  Lb→ w +(Lβ) q ←Lx
      ↓    ↓    ↓      ↓    ↓    ↓     ↓     ↓         ↓
      Lc → t ← Lγ      Lγ → r ← Lz     Lc→ t +(Lγ) r ←Lx
   """
  function composeH(r₁::OpenRule, r₂::OpenRule)::OpenRule
    @assert r₁.right == r₂.left
    top = compose(r₁.top, r₂.top)
    middle = compose(r₁.middle, r₂.middle)
    bottom = compose(r₁.bottom, r₂.bottom)
    iD, iF = pushout(right(r₁.top), left(r₂.top)); # upper composite
    iD_, iF_ = pushout(right(r₁.bottom), left(r₂.bottom)); # lower composite
    colim  = pushout(right(r₁.middle), left(r₂.middle)); # middle composite
    ad, bf = left(r₁.center), left(r₂.center); # center 'upward' arrows in the square
    ad_, bf_ = right(r₁.center), right(r₂.center); # center 'upward' arrows in the square
    upspan = Multicospan([compose(ad,iD), compose(bf,iF)]);
    downspan = Multicospan([compose(ad_,iD_), compose(bf_,iF_)]);
    up, down = [universal(colim, sp) for sp in [upspan, downspan]]
    return OpenRule(top, middle, bottom, r₁.left, Span(up, down), r₂.right)
  end

  """    composeV(r₁, r₂)

  compose two rewrite rules vertically as shown below:
      La → v ← Lα      Lc → x ← Lγ
      ↑    ↑    ↑      ↑    ↑    ↑
      Lb → w ← Lβ  ∘v  Ld → y ← Lψ
      ↓    ↓    ↓      ↓    ↓    ↓
      Lc → x ← Lγ      Le → z ← Lϕ

         La    →    v   ←    Lα
         ↑          ↑         ↑
  =  L(b ×c d) → w ×x y ← L(β ×γ ψ)
         ↓          ↓         ↓
         Le    →    z   ←    Lϕ
  """
  function composeV(r₁::OpenRule, r₂::OpenRule)::OpenRule
    @assert r₁.bottom == r₂.top
    lft = composeV(r₁.left, r₂.left);
    rght = composeV(r₁.right, r₂.right);
    center = composeV(r₁.center, r₂.center);
    lim = pullback(right(r₁.center), left(r₂.center));
    iB,iD = pullback(right(r₁.left), left(r₂.left));
    iβ,iψ = pullback(right(r₁.right), left(r₂.right));
    leftspan = Multispan([compose(iB, left(r₁.middle),),
                          compose(iD, left(r₂.middle))]);
    rightspan = Multispan([compose(iβ, right(r₁.middle)),
                           compose(iψ, right(r₂.middle),)]);
    middleleft = universal(lim, leftspan);
    middleright = universal(lim, rightspan);
    middle = OpenGraph(apex(center), middleleft[:V], middleright[:V]);
    return OpenRule(r₁.top, middle, r₂.bottom, lft, center, rght)
  end
end
end
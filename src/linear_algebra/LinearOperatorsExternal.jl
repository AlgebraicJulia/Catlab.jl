# External packages.
using .LinearOperators
using .LinearOperators: opEye, opExtension, opRestriction, opZeros


@auto_hash_equals struct LinearOpDom
  N::Int
end

@instance LinearFunctions{LinearOpDom, LinearOperator} begin
  @import adjoint, +

  dom(f::LinearOperator) = LinearOpDom(size(f,2))
  codom(f::LinearOperator) = LinearOpDom(size(f,1))

  compose(f::LinearOperator, g::LinearOperator) = g*f
  id(V::LinearOpDom) = opEye(V.N)

  oplus(V::LinearOpDom, W::LinearOpDom) = LinearOpDom(V.N + W.N)
  oplus(f::LinearOperator, g::LinearOperator) = begin
    dom_total   = size(f,2) + size(g,2)
    codom_total = size(f,1) + size(g,1)
    dom_f   = 1:size(f,2)
    codom_f = 1:size(f,1)
    dom_g   = (size(f,2)+1):dom_total
    codom_g = (size(f,1)+1):codom_total
    fOp = opExtension(codom_f, codom_total)*f*opRestriction(dom_f,dom_total)
    gOp = opExtension(codom_g, codom_total)*g*opRestriction(dom_g,dom_total)
    fOp + gOp
  end
  mzero(::Type{LinearOpDom}) = LinearOpDom(0)
  swap(V::LinearOpDom, W::LinearOpDom) =
    opExtension(1:W.N, V.N+W.N) * opRestriction((V.N+1):(V.N+W.N),V.N+W.N) +
    opExtension((W.N+1):(V.N+W.N), V.N+W.N) * opRestriction(1:V.N,V.N+W.N)
  mcopy(V::LinearOpDom) =
    opExtension(1:V.N, 2*V.N)+opExtension((V.N+1):(2*V.N), 2*V.N)
  delete(V::LinearOpDom) = opZeros(0, V.N)
  plus(V::LinearOpDom) =
    opRestriction(1:V.N, 2*V.N)+opRestriction((V.N+1):(2*V.N), 2*V.N)
  zero(V::LinearOpDom) = opZeros(V.N, 0)

  plus(f::LinearOperator, g::LinearOperator) = f+g
  scalar(V::LinearOpDom, c::Number) = opEye(typeof(c),V.N)*c
  antipode(V::LinearOpDom) = scalar(V,-1)

  pair(f::LinearOperator, g::LinearOperator) = mcopy(dom(f)) ⋅ (f ⊕ g)
  copair(f::LinearOperator, g::LinearOperator) = (f ⊕ g) ⋅ plus(codom(f))
  proj1(A::LinearOpDom, B::LinearOpDom) = id(A) ⊕ delete(B)
  proj2(A::LinearOpDom, B::LinearOpDom) = delete(A) ⊕ id(B)
  coproj1(A::LinearOpDom, B::LinearOpDom) = id(A) ⊕ zero(B)
  coproj2(A::LinearOpDom, B::LinearOpDom) = zero(A) ⊕ id(B)
end

using ..GAT
using ..Syntax
import ..Syntax: show_infix, show_latex

# Monoidal category
###################

""" Doctrine of *monoidal category*

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
signature for weak monoidal categories later.
"""
@signature Category(Ob,Hom) => MonoidalCategory(Ob,Hom) begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::Hom(A,B), g::Hom(C,D))::Hom(otimes(A,C),otimes(B,D)) <=
    (A::Ob, B::Ob, C::Ob, D::Ob)
  munit()::Ob

  # Extra syntax
  otimes(As::Vararg{Ob}) = foldl(otimes, As)
  otimes(fs::Vararg{Hom}) = foldl(otimes, fs)

  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Hom, g::Hom) = otimes(f, g)
  ⊗(As::Vararg{Ob}) = otimes(As...)
  ⊗(fs::Vararg{Hom}) = otimes(fs...)
end

function show_infix(io::IO, expr::ObExpr{:otimes}; kw...)
  show_infix(io, expr, "⊗"; kw...)
end
function show_infix(io::IO, expr::HomExpr{:otimes}; kw...)
  show_infix(io, expr, "⊗"; kw...)
end
show_infix(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

function show_latex(io::IO, expr::ObExpr{:otimes}; kw...)
  show_latex_infix(io, expr, "\\otimes"; kw...)
end
function show_latex(io::IO, expr::HomExpr{:otimes}; kw...)
  show_latex_infix(io, expr, "\\otimes"; kw...)
end
show_latex(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

# Symmetric monoidal category
#############################

""" Doctrine of *symmetric monoidal category*

The signature (but not the axioms) is the same as a braided monoidal category.
"""
@signature MonoidalCategory(Ob,Hom) => SymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::Hom(otimes(A,B),otimes(B,A))
end

@syntax FreeSymmetricMonoidalCategory(ObExpr,HomExpr) SymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(:munit, Super.otimes(A,B))
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

# (Co)cartesian category
########################

""" Doctrine of *cartesian category*

Actually, this is a cartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => CartesianCategory(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  delete(A::Ob)::Hom(A,munit())
  
  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
end

@syntax FreeCartesianCategory(ObExpr,HomExpr) CartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(:munit, Super.otimes(A,B))
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

""" Doctrine of *cocartesian category*

Actually, this is a cocartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => CocartesianCategory(Ob,Hom) begin
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  create(A::Ob)::Hom(munit(),A)
  
  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  □(A::Ob) = create(A)
end

@syntax FreeCocartesianCategory(ObExpr,HomExpr) CocartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(:munit, Super.otimes(A,B))
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

# Compact closed category
#########################

""" Doctrine of *compact closed category*
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => CompactClosedCategory(Ob,Hom) begin
  dual(A::Ob)::Ob
  
  ev(A::Ob)::Hom(otimes(A,dual(A)), munit())
  coev(A::Ob)::Hom(munit(), otimes(dual(A),A))
end

@syntax FreeCompactClosedCategory(ObExpr,HomExpr) CompactClosedCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(:munit, Super.otimes(A,B))
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

# Dagger category
#################

""" Doctrine of *dagger category*
"""
@signature Category(Ob,Hom) => DaggerCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

""" Doctrine of *dagger compact category*

FIXME: This signature should extend both `DaggerCategory` and
`CompactClosedCategory`, but we don't support multiple inheritance yet.
"""
@signature CompactClosedCategory(Ob,Hom) => DaggerCompactCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@syntax FreeDaggerCompactCategory(ObExpr,HomExpr) DaggerCompactCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(:munit, Super.otimes(A,B))
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

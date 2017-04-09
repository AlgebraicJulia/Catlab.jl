import Lazy: @>

using ..GAT
using ..Syntax
import ..Syntax: show_unicode, show_latex

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

function show_unicode(io::IO, expr::ObExpr{:otimes}; kw...)
  show_unicode_infix(io, expr, "⊗"; kw...)
end
function show_unicode(io::IO, expr::HomExpr{:otimes}; kw...)
  show_unicode_infix(io, expr, "⊗"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

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
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

function show_latex(io::IO, expr::HomExpr{:braid}; kw...)
  show_latex_script(io, expr, "\\sigma")
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
  
  pair(f::Hom(A,B), g::Hom(A,C))::Hom(A,otimes(B,C)) <= (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::Hom(otimes(A,B),A)
  proj2(A::Ob, B::Ob)::Hom(otimes(A,B),B)
  
  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
end

""" Syntax for a free cartesian category.

In this syntax, the pairing and projection operations are defined using
duplication and deletion, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCartesianCategory(ObExpr,HomExpr) CartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mcopy}; kw...)
  show_latex_script(io, expr, "\\Delta")
end
function show_latex(io::IO, expr::HomExpr{:delete}; kw...)
  show_latex_script(io, expr, "\\lozenge")
end

""" Doctrine of *cocartesian category*

Actually, this is a cocartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => CocartesianCategory(Ob,Hom) begin
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  create(A::Ob)::Hom(munit(),A)
  
  copair(f::Hom(A,C), g::Hom(B,C))::Hom(otimes(A,B),C) <= (A::Ob, B::Ob, C::Ob)
  in1(A::Ob, B::Ob)::Hom(A,otimes(A,B))
  in2(A::Ob, B::Ob)::Hom(B,otimes(A,B))
  
  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  □(A::Ob) = create(A)
end

""" Syntax for a free cocartesian category.

In this syntax, the copairing and inclusion operations are defined using
merging and creation, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCocartesianCategory(ObExpr,HomExpr) CocartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  copair(f::Hom, g::Hom) = compose(otimes(f,g), mmerge(codom(f)))
  in1(A::Ob, B::Ob) = otimes(id(A), create(B))
  in2(A::Ob, B::Ob) = otimes(create(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mmerge}; kw...)
  show_latex_script(io, expr, "\\nabla")
end
function show_latex(io::IO, expr::HomExpr{:create}; kw...)
  show_latex_script(io, expr, "\\square")
end

# Biproduct category
####################

""" Doctrine of *bicategory category*

Also known as a *semiadditive category*.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => BiproductCategory(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  delete(A::Ob)::Hom(A,munit())
  create(A::Ob)::Hom(munit(),A)
  
  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
  □(A::Ob) = create(A)
end

@syntax FreeBiproductCategory(ObExpr,HomExpr) BiproductCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
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
  dual(A::Ob) = anti_involute(Super.dual(A), dual, otimes, munit)
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

function show_latex(io::IO, expr::ObExpr{:dual}; kw...)
  show_latex(io, first(expr))
  print(io, "^*")
end
function show_latex(io::IO, expr::HomExpr{:ev}; kw...)
  show_latex_script(io, expr, "\\mathrm{ev}")
end
function show_latex(io::IO, expr::HomExpr{:coev}; kw...)
  show_latex_script(io, expr, "\\mathrm{coev}")
end

# Dagger category
#################

""" Doctrine of *dagger category*
"""
@signature Category(Ob,Hom) => DaggerCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@syntax FreeDaggerCategory(ObExpr,HomExpr) DaggerCategory begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  dagger(f::Hom) = anti_involute(Super.dagger(f), dagger, compose, id)
end

""" Doctrine of *dagger compact category*

FIXME: This signature should extend both `DaggerCategory` and
`CompactClosedCategory`, but we don't support multiple inheritance yet.
"""
@signature CompactClosedCategory(Ob,Hom) => DaggerCompactCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@syntax FreeDaggerCompactCategory(ObExpr,HomExpr) DaggerCompactCategory begin
  dual(A::Ob) = anti_involute(Super.dual(A), dual, otimes, munit)
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  dagger(f::Hom) = @>(Super.dagger(f),
    anti_involute(dagger, compose, id),
    distribute_unary(dagger, otimes))
end

function show_latex(io::IO, expr::HomExpr{:dagger}; kw...)
  f = first(expr)
  if (head(f) != :generator) print(io, "\\left(") end
  show_latex(io, f)
  if (head(f) != :generator) print(io, "\\right)") end
  print(io, "^\\dagger")
end

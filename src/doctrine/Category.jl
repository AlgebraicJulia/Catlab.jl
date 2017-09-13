import Base: show, ∘

# Category
##########

""" Doctrine of *category* (with no extra structure)

**Warning**: We compose functions from left to right, i.e., if f:A→B and g:B→C
then compose(f,g):A→C. Under this convention function are applied on the right,
e.g., if a∈A then af∈B.

We retain the usual meaning of the symbol ∘, i.e., g∘f = compose(f,g).
This usage is too entrenched to overturn, however inconvenient it may be.
"""
@signature Category(Ob,Hom) begin
  """ Object in a category """
  Ob::TYPE
  
  """ Morphism in a category """
  Hom(dom::Ob,codom::Ob)::TYPE
  
  id(A::Ob)::Hom(A,A)
  compose(f::Hom(A,B), g::Hom(B,C))::Hom(A,C) <= (A::Ob, B::Ob, C::Ob)
  
  # Convenience constructors
  compose(fs::Vararg{Hom}) = foldl(compose, fs)
  
  # Unicode syntax
  ∘(f::Hom, g::Hom) = compose(g, f)
  ∘(fs::Vararg{Hom}) = foldl(∘, fs)
end

# Convenience constructors not requiring type dispatch
compose(fs::Vector) = foldl(compose, fs)

@syntax FreeCategory(ObExpr,HomExpr) Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

function show_unicode(io::IO, expr::HomExpr{:compose}; kw...)
  show_unicode_infix(io, expr, "⋅"; kw...)
end

function show_latex(io::IO, expr::HomExpr{:id}; kw...)
  show_latex_script(io, expr, "\\mathrm{id}")
end
function show_latex(io::IO, expr::HomExpr{:compose}; paren::Bool=false, kw...)
  show_latex_infix(io, expr, "\\cdot"; paren=paren)
end

function show(io::IO, ::MIME"text/latex", expr::BaseExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, "\$")
end

function show(io::IO, ::MIME"text/latex", expr::HomExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, " : ")
  show_latex(io, dom(expr))
  print(io, " \\to ")
  show_latex(io, codom(expr))
  print(io, "\$")
end

# 2-category
############

""" Doctrine of (strict) *2-category*
"""
@signature Category(Ob,Hom) => Category2(Ob,Hom,Hom2) begin
  """ 2-morphism in a 2-category """
  Hom2(dom::Hom(A,B), codom::Hom(A,B))::TYPE <= (A::Ob, B::Ob)
  
  # Hom categories: Vertical composition
  id(f)::Hom2(f,f) <= (A::Ob, B::Ob, f::Hom(A,B))
  compose(α::Hom2(f,g), β::Hom2(g,h))::Hom2(f,h) <=
    (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B), h::Hom(A,B))
  
  # Horizontal compostion
  compose2(α::Hom2(f,g), β::Hom2(h,k))::Hom2(compose(f,h),compose(g,k)) <=
    (A::Ob, B::Ob, C::Ob, f::Hom(A,B), g::Hom(A,B), h::Hom(B,C), k::Hom(B,C))
  
  # Convenience constructors
  compose(αs::Vararg{Hom2}) = foldl(compose, αs)
  compose2(αs::Vararg{Hom2}) = foldl(compose2, αs)
  
  # Unicode syntax
  ∘(α::Hom2, β::Hom2) = compose(β, α)
  ∘(αs::Vararg{Hom2}) = foldl(∘, αs)
end

# Convenience constructors not requiring type dispatch
compose2(αs::Vector) = foldl(compose2, αs)

""" Syntax for a 2-category.

Checks domains of morphisms but not 2-morphisms.
"""
@syntax FreeCategory2(ObExpr,HomExpr,Hom2Expr) Category2 begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  compose(α::Hom2, β::Hom2) = associate(Super.compose(α,β))
  compose2(α::Hom2, β::Hom2) = associate(Super.compose2(α,β))
end

function show_unicode(io::IO, expr::Hom2Expr{:compose}; kw...)
  show_unicode_infix(io, expr, "⋅"; kw...)
end
function show_unicode(io::IO, expr::Hom2Expr{:compose2}; kw...)
  show_unicode_infix(io, expr, "*"; kw...)
end

function show_latex(io::IO, expr::Hom2Expr{:compose}; kw...)
  show_latex_infix(io, expr, "\\cdot"; kw...)
end
function show_latex(io::IO, expr::Hom2Expr{:compose2}; kw...)
  show_latex_infix(io, expr, "*"; kw...)
end

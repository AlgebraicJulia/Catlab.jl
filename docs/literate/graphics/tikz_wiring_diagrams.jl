# # Wiring diagrams in TikZ
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/tikz_wiring_diagrams.ipynb)
#
# Catlab can draw morphism expressions as TikZ pictures. To use this feature,
# you must import the [TikzPictures.jl](https://github.com/sisl/TikzPictures.jl)
# package before loading `Catlab.Graphics`.

import TikzPictures
using Catlab.Graphics

# ### Symmetric monoidal category

using Catlab.Doctrines

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A)
h = Hom(:h, otimes(A,B), otimes(A,B));
#-
to_tikz(f; arrowtip="Stealth", labels=true)
#-
to_tikz(compose(f,g); arrowtip="Stealth", labels=true)
#-
comp1 = compose(otimes(g,f), h, otimes(f,g))
#-
to_tikz(comp1)
#-
comp2 = compose(otimes(id(A),f), h, otimes(id(A),g))
#-
to_tikz(comp2)
#-
to_tikz(Hom(:H, otimes(A,A), otimes(B,B,B)))
#-
twist = compose(braid(A,A), otimes(f,f), braid(B,B))
#-
to_tikz(twist)

# ### Biproduct category

A, B = Ob(FreeBiproductCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A);
#-
split = compose(mcopy(A), otimes(f,f))
#-
to_tikz(split)
#-
combine = compose(split, mmerge(B))
#-
to_tikz(combine, labels=true)
#-
to_tikz(compose(create(A), f, g, delete(A)))

# ### Compact closed category 

A, B = Ob(FreeCompactClosedCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A)
h = Hom(:h, otimes(A,B), otimes(A,B));
#-
to_tikz(dcounit(A); arrowtip="Stealth", labels=true)
#-
to_tikz(dunit(A); arrowtip="Stealth", labels=true)
#-
transpose = compose(
  otimes(dunit(A), id(dual(B))),
  otimes(id(dual(A)), f, id(dual(B))),
  otimes(id(dual(A)), dcounit(B)),
)
#-
to_tikz(transpose)
#-
trace = compose(
  f,
  otimes(dunit(A), id(B)),
  otimes(id(dual(A)), h),
  otimes(braid(dual(A),A), id(B)),
  otimes(dcounit(A), id(B)),
  g
)
#-
to_tikz(trace)

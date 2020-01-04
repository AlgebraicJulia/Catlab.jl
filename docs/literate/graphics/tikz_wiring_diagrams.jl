# # Wiring diagrams in TikZ
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/tikz_wiring_diagrams.ipynb)
#
# Catlab can draw morphism expressions as TikZ pictures. To use this feature,
# LaTeX must be installed and the Julia package
# [TikzPictures.jl](https://github.com/sisl/TikzPictures.jl) must be imported
# before Catlab is loaded.

import TikzPictures
using Catlab.WiringDiagrams, Catlab.Graphics

# ## Examples

# ### Symmetric monoidal category

using Catlab.Doctrines

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f, g = Hom(:f, A, B), Hom(:g, B, A);

# To start, here are a few very simple examples.

to_tikz(f, labels=true)
#-
to_tikz(f⋅g, labels=true)
#-
to_tikz(f⊗g, labels=true, orientation=TopToBottom)

# Here is a more complex example, involving generators with compound domains and
# codomains.

h, k = Hom(:h, C, D),  Hom(:k, D, C)
m, n = Hom(:m, B⊗A, A⊗B), Hom(:n, D⊗C, C⊗D)
q = Hom(:l, A⊗B⊗C⊗D, D⊗C⊗B⊗A)

to_tikz((f⊗g⊗h⊗k)⋅(m⊗n)⋅q⋅(n⊗m)⋅(h⊗k⊗f⊗g))

# Identities and braidings appear as wires.

to_tikz(id(A), labels=true)
#-
to_tikz(braid(A,B), labels=true, labels_pos=0.25)
#-
to_tikz(braid(A,B) ⋅ (g⊗f) ⋅ braid(A,B))

# The isomorphism $A \otimes B \otimes C \to C \otimes B \otimes A$ induced by
# the permutation $(3\ 2\ 1)$ is a composite of braidings and identities.

to_tikz((braid(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ braid(A,C) ⋅ (braid(B,C) ⊗ id(A))),
        arrowtip="Stealth", arrowtip_pos=1.0, labels=true, labels_pos=0.0)

# ### Biproduct category

A, B = Ob(FreeBiproductCategory, :A, :B)
f = Hom(:f, A, B)

to_tikz(mcopy(A), labels=true)
#-
to_tikz(delete(A), labels=true)
#-
to_tikz(mcopy(A)⋅(f⊗f)⋅mmerge(B), labels=true)

# ### Compact closed category

# The unit and co-unit of a compact closed category appear as caps and cups.

A, B = Ob(FreeCompactClosedCategory, :A, :B)

to_tikz(dunit(A), arrowtip="Stealth")
#-
to_tikz(dcounit(A), arrowtip="Stealth")

# In a self-dual compact closed category, such as a bicategory of relations,
# every morphism $f: A \to B$ has a transpose $f^\dagger: B \to A$ given by
# bending wires:

A, B = Ob(FreeBicategoryRelations, :A, :B)
f = Hom(:f, A, B)

to_tikz((dunit(A) ⊗ id(B)) ⋅ (id(A) ⊗ f ⊗ id(B)) ⋅ (id(A) ⊗ dcounit(B)))

# ## Custom styles

# The visual appearance of wiring diagrams can be customized using the builtin
# options or by redefining the TikZ styles for the boxes or wires.

import Catlab.Graphics: TikZ

A, B, = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

pic = to_tikz(f⋅g, styles=Dict(
  "box" => [
    TikZ.Property("draw"),
    TikZ.Property("fill", "{rgb,255: red,230; green,230; blue,250}"),
  ],
))

# ## Output formats

# The function `to_tikz` returns an object of type `TikZ.Picture`, representing
# a TikZ picture has an abstract syntax tree. When displayed interactively, this
# object is compiled by LaTeX to PDF and then converted to SVG.

# To generate the LaTeX source code, use the builtin pretty-printer. This
# feature does not require LaTeX or TikzPictures.jl to be installed.

pic = to_tikz(f⋅g)
TikZ.pprint(pic)

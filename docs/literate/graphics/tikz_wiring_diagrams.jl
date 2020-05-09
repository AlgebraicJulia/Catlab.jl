# # Drawing wiring diagrams in TikZ
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/tikz_wiring_diagrams.ipynb)
#
# Catlab can draw morphism expressions as TikZ pictures. To use this feature,
# LaTeX must be installed and the Julia package
# [TikzPictures.jl](https://github.com/sisl/TikzPictures.jl) must be loaded.
#
# For best results, it is recommended to load the packages
# [Convex.j](https://github.com/JuliaOpt/Convex.jl) and
# [SCS.jl](https://github.com/JuliaOpt/SCS.jl). When available they are used to
# optimize the layout of the outer ports.

using Catlab.WiringDiagrams, Catlab.Graphics

import Convex, SCS
import TikzPictures

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

σ = (braid(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ braid(A,C) ⋅ (braid(B,C) ⊗ id(A)))

to_tikz(σ, arrowtip="Stealth", arrowtip_pos="-0.1pt",
        labels=true, labels_pos="0.1pt")

# By default, anchor points are added along identity and braiding wires to
# reproduce the expression structure in the layout. The anchors can be disabled
# to get a more "unbiased" layout.

to_tikz(σ, anchor_wires=false, arrowtip="Stealth", arrowtip_pos="-0.1pt",
        labels=true, labels_pos="0.1pt")

# ### Biproduct category

A, B, C = Ob(FreeBiproductCategory, :A, :B, :C)
f = Hom(:f, A, B)

to_tikz(mcopy(A), labels=true)
#-
to_tikz(delete(A), labels=true)
#-
to_tikz(mcopy(A)⋅(f⊗f)⋅mmerge(B), labels=true)
#-
to_tikz(mcopy(A⊗B), orientation=TopToBottom, labels=true)
#-
to_tikz(mcopy(A⊗B⊗C), orientation=TopToBottom, labels=true)

# ### Compact closed category

# The unit and co-unit of a compact closed category appear as caps and cups.

A, B = Ob(FreeCompactClosedCategory, :A, :B)

to_tikz(dunit(A), arrowtip="Stealth", labels=true)
#-
to_tikz(dcounit(A), arrowtip="Stealth", labels=true)

# In a self-dual compact closed category, such as a bicategory of relations,
# every morphism $f: A \to B$ has a transpose $f^\dagger: B \to A$ given by
# bending wires:

A, B = Ob(FreeBicategoryRelations, :A, :B)
f = Hom(:f, A, B)

to_tikz((dunit(A) ⊗ id(B)) ⋅ (id(A) ⊗ f ⊗ id(B)) ⋅ (id(A) ⊗ dcounit(B)))

# ### Abelian bicategory of relations

# In an abelian bicategory of relations, such as the category of linear
# relations, the duplication morphisms $\Delta_X: X \to X \otimes X$ and
# addition morphisms $\blacktriangledown_X: X \otimes X \to X$ belong to a
# bimonoid. Among other things, this means that the following two morphisms are
# equal.

X = Ob(FreeAbelianBicategoryRelations, :X)

to_tikz(plus(X) ⋅ mcopy(X))
#-
to_tikz((mcopy(X)⊗mcopy(X)) ⋅ (id(X)⊗braid(X,X)⊗id(X)) ⋅ (plus(X)⊗plus(X)))

# ## Custom styles

# The visual appearance of wiring diagrams can be customized using the builtin
# options or by redefining the TikZ styles for the boxes or wires.

A, B, = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

pic = to_tikz(f⋅g, styles=Dict(
  "box" => ["draw", "fill"=>"{rgb,255: red,230; green,230; blue,250}"],
))
#-
X = Ob(FreeAbelianBicategoryRelations, :X)

to_tikz(plus(X) ⋅ mcopy(X), styles=Dict(
  "junction" => ["circle", "draw", "fill"=>"red", "inner sep"=>"0"],
  "variant junction" => ["circle", "draw", "fill"=>"blue", "inner sep"=>"0"],
))

# By default, the boxes are rectangular (`:rectangle`). Other available shapes
# include circles (`:circle`), ellipses (`:ellipse`), triangles (`:triangle`,
# `:invtriangle`), and trapezoids (`:trapezium`, `:invtrapezium`).

to_tikz(f⋅g, default_box_shape=:circle)
#-
to_tikz(f⋅g, rounded_boxes=false, box_shapes=Dict(
  f => :triangle, g => :invtriangle,
))
#-
to_tikz(f⋅g, orientation=TopToBottom, rounded_boxes=false, box_shapes=Dict(
  f => :triangle, g => :invtriangle,
))
#-
to_tikz(f⋅g, box_shapes=Dict(
  f => :invtrapezium, g => :trapezium,
))

# ## Output formats

# The function `to_tikz` returns an object of type `TikZ.Document`, representing
# a TikZ picture and its TikZ library dependencies as an abstract syntax tree.
# When displayed interactively, this object is compiled by LaTeX to PDF and then
# converted to SVG.

# To generate the LaTeX source code, use the builtin pretty-printer. This
# feature does not require LaTeX or TikzPictures.jl to be installed.

import Catlab.Graphics: TikZ

doc = to_tikz(f⋅g)
TikZ.pprint(doc)

# # Drawing wiring diagrams using Compose.jl
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/composejl_wiring_diagrams.ipynb)
#
# Catlab can draw wiring diagrams using the Julia package
# [Compose.jl](https://github.com/GiovineItalia/Compose.jl).

using Catlab.WiringDiagrams, Catlab.Graphics

# ### Symmetric monoidal category

using Catlab.Doctrines

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f, g = Hom(:f, A, B), Hom(:g, B, A);

# To start, here are a few very simple examples.

to_composejl(f)
#-
to_composejl(f⋅g)
#-
to_composejl(f⊗g)

# A more complex example, using generators with compound domains and codomains.

h, k = Hom(:h, C, D),  Hom(:k, D, C)
m, n = Hom(:m, B⊗A, A⊗B), Hom(:n, D⊗C, C⊗D)
q = Hom(:l, A⊗B⊗C⊗D, D⊗C⊗B⊗A)

to_composejl((f⊗g⊗h⊗k)⋅(m⊗n)⋅q⋅(n⊗m)⋅(h⊗k⊗f⊗g))

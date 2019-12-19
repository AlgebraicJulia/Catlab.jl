# # Drawing wiring diagrams using Compose.jl
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/composejl_wiring_diagrams.ipynb)
#
# Catlab can draw wiring diagrams using the Julia package
# [Compose.jl](https://github.com/GiovineItalia/Compose.jl)

using Catlab.WiringDiagrams, Catlab.Graphics

# ### Symmetric monoidal category

using Catlab.Doctrines

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A)
h = Hom(:h, otimes(A,B), otimes(A,B));

# To start, here are a few very simple examples.

to_composejl(f)
#-
to_composejl(compose(f,g))
#-
to_composejl(otimes(f,g))

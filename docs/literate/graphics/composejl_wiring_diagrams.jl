# # Wiring diagrams in Compose.jl
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/composejl_wiring_diagrams.ipynb)
#
# Catlab can draw wiring diagrams using the Julia package
# [Compose.jl](https://github.com/GiovineItalia/Compose.jl).

using Catlab.WiringDiagrams, Catlab.Graphics

# ## Examples

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

# Here is a more complex example, involving generators with compound domains and
# codomains.

h, k = Hom(:h, C, D),  Hom(:k, D, C)
m, n = Hom(:m, B⊗A, A⊗B), Hom(:n, D⊗C, C⊗D)
q = Hom(:l, A⊗B⊗C⊗D, D⊗C⊗B⊗A)

to_composejl((f⊗g⊗h⊗k)⋅(m⊗n)⋅q⋅(n⊗m)⋅(h⊗k⊗f⊗g))

# Identities and braidings appear as wires.

to_composejl(id(A))
#-
to_composejl(braid(A,B))
#-
to_composejl(braid(A,B) ⋅ (g⊗f) ⋅ braid(A,B))

# The isomorphism $A \otimes B \otimes C \to C \otimes B \otimes A$ induced by
# the permutation $(3\ 2\ 1)$ is a composite of braidings and identities.

to_composejl((braid(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ braid(A,C) ⋅ (braid(B,C) ⊗ id(A))))

# ### Biproduct category

A, B = Ob(FreeBiproductCategory, :A, :B)
f = Hom(:f, A, B)

to_composejl(mcopy(A))
#-
to_composejl(delete(A))
#-
to_composejl(mcopy(A)⋅(f⊗f)⋅mmerge(B))

# ### Compact closed category

# The unit and co-unit of a compact closed category appear as caps and cups.

A, B = Ob(FreeCompactClosedCategory, :A, :B)

to_composejl(dunit(A))
#-
to_composejl(dcounit(A))

# In a self-dual compact closed category, such as a bicategory of relations,
# every morphism $f: A \to B$ has a transpose $f^\dagger: B \to A$ given by
# bending wires:

A, B = Ob(FreeBicategoryRelations, :A, :B)
f = Hom(:f, A, B)

to_composejl((dunit(A) ⊗ id(B)) ⋅ (id(A) ⊗ f ⊗ id(B)) ⋅ (id(A) ⊗ dcounit(B)))

# ## Custom styles

# The visual appearance of wiring diagrams can be customized by passing Compose
# [properties](http://giovineitalia.github.io/Compose.jl/latest/gallery/properties/).

using Compose: fill, stroke

A, B, = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

to_composejl(f⋅g, box_props=[fill("lavender"), stroke("black")])

# ## Output formats

# The function `to_composejl` returns a `ComposePicture` object, which contains
# a Compose.jl context as well as a recommended width and height. When displayed
# interactively, this object is rendered using Compose's SVG backend.

# Any backend can be used by calling Compose's `draw` function. The SVG and
# [PGF](https://ctan.org/pkg/pgf) (LaTeX) backends are always available. To use
# the PNG or PDF backends, the extra packages
# [Cairo.jl](https://github.com/JuliaGraphics/Cairo.jl) and
# [Fontconfig.jl](https://github.com/JuliaGraphics/Fontconfig.jl) must be
# installed.

# For example, here is how to use the PGF backend.

using Compose: draw, PGF

pic = to_composejl(f⋅g, rounded_boxes=false)
pgf = sprint() do io
  pgf_backend = PGF(io, pic.width, pic.height,
    false, # emit_on_finish
    true,  # only_tikz
    texfonts=true)
  draw(pgf_backend, pic.context)
end
println(pgf)

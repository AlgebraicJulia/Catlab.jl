# # Algebraic networks
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/experimental/algebraic_nets.ipynb)
#

using Catlab, Catlab.Doctrines, Catlab.Graphics
using Catlab.Experimental.AlgebraicNets
using Catlab.Experimental.MathFormulas

import TikzPictures
#-
R = Ob(AlgebraicNet, "\\mathbb{R}")
f_sin = Hom(:sin, R, R)
f_cos = Hom(:cos, R, R)
display(f_sin)
display(f_cos)
#-
f = compose(mcopy(R),otimes(f_sin,f_cos),mmerge(R))
#-
to_tikz(f, labels=true)
#-
compile_expr(f; args=[:x])
#-
to_formula(f, [:x])
#-
f = compose(mcopy(R,3), otimes(f_sin, f_cos, f_sin))
#-
to_tikz(f)
#-
compile_expr(f; args=[:x])
#-
f = compose(linear(2,R,R), f_sin, linear(2,R,R))
#-
to_tikz(f)
#-
compile_expr(f; args=[:x])
#-
to_formula(f, [:x])
#-
f = compose(mcopy(R), otimes(id(R),Hom(:cos,R,R)), Hom(:*,otimes(R,R),R))
#-
to_tikz(f)
#-
compile_expr(f; args=[:x])
#-
to_formula(f, [:x])

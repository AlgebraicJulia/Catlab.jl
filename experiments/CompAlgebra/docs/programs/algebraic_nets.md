```@meta
EditURL = "https://github.com/epatters/Catlab.jl/blob/master/docs/docs/literate/programs/algebraic_nets.jl"
```

# Algebraic networks

[![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](https://nbviewer.jupyter.org/github/epatters/Catlab.jl/blob/gh-pages/v0.5.2/generated/programs/algebraic_nets.ipynb)

```@example algebraic_nets
using Catlab.Programs

import TikzPictures
using Catlab.Graphics
```

```@example algebraic_nets
R = Ob(AlgebraicNet, "\\mathbb{R}")
f_sin = Hom(:sin, R, R)
f_cos = Hom(:cos, R, R)
display(f_sin)
display(f_cos)
```

```@example algebraic_nets
f = compose(mcopy(R),otimes(f_sin,f_cos),mmerge(R))
```

```@example algebraic_nets
to_tikz(f, labels=true)
```

```@example algebraic_nets
compile_expr(f; args=[:x])
```

```@example algebraic_nets
to_formula(f, [:x])
```

```@example algebraic_nets
f = compose(mcopy(R,3), otimes(f_sin, f_cos, f_sin))
```

```@example algebraic_nets
to_tikz(f)
```

```@example algebraic_nets
compile_expr(f; args=[:x])
```

```@example algebraic_nets
f = compose(linear(2,R,R), f_sin, linear(2,R,R))
```

```@example algebraic_nets
to_tikz(f)
```

```@example algebraic_nets
compile_expr(f; args=[:x])
```

```@example algebraic_nets
to_formula(f, [:x])
```

```@example algebraic_nets
f = compose(mcopy(R), otimes(id(R),Hom(:cos,R,R)), Hom(:*,otimes(R,R),R))
```

```@example algebraic_nets
to_tikz(f)
```

```@example algebraic_nets
compile_expr(f; args=[:x])
```

```@example algebraic_nets
to_formula(f, [:x])
```


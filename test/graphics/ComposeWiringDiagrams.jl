module TestComposeWiringDiagrams

using Test
import Compose

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Graphics

is_pic(x) = x isa ComposePicture

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

@test is_pic(to_composejl(f))
@test is_pic(to_composejl(id(A)))
@test is_pic(to_composejl(compose(f,g)))
@test is_pic(to_composejl(otimes(f,g)))

end

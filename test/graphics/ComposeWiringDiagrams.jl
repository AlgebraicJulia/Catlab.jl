module TestComposeWiringDiagrams

using Test
import Compose

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab: Graphics

to_composejl(f; kw...) = Graphics.to_composejl(f; outer_ports_layout=:fixed, kw...)

function tagged(ctx::Compose.Context, tag::Symbol)
  vcat(ctx.tag == tag ? [ctx] : [],
       mapreduce(c -> tagged(c, tag), vcat, ctx.container_children; init=[]))
end
tagged(pic::Graphics.ComposePicture, tag::Symbol) = tagged(pic.context, tag)

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

pic = to_composejl(f)
@test length(tagged(pic, :box)) == 1
@test length(tagged(pic, :wire)) == 2

pic = to_composejl(id(A))
@test length(tagged(pic, :box)) == 0
@test length(tagged(pic, :wire)) == 1

pic = to_composejl(compose(f,g))
@test length(tagged(pic, :box)) == 2
@test length(tagged(pic, :wire)) == 3

pic = to_composejl(otimes(f,g))
@test length(tagged(pic, :box)) == 2
@test length(tagged(pic, :wire)) == 4

pic = to_composejl(braid(A,B))
@test length(tagged(pic, :box)) == 0
@test length(tagged(pic, :wire)) == 2

A, B = Ob(FreeBiproductCategory, :A, :B)

for expr in (mcopy(A), delete(A), mmerge(A), create(A))
  pic = to_composejl(expr)
  @test length(tagged(pic, :box)) == 1
end

end

#using Pkg
#Pkg.activate("../../")

#Pkg.instantiate()

using Test
using Catlab
using Catlab.Doctrines
using Catlab.Syntax

using Catlab.Graphics
using Catlab.Graphics.TikZ

using Catlab.WiringDiagrams

import Catlab.Doctrines: Ob, Hom

wd(x) = to_wiring_diagram(x)

display(x) = to_graphviz(add_junctions!(wd(x)), orientation=LeftToRight)

R = Ob(FreeAbelianBicategoryRelations, :ℝ)

f = Hom(:f, R,R)

display(otimes(f,f))

ex = mcopy(R)⋅otimes(f,f)⋅mplus(R)

display(ex)

^(x::FreeBiproductCategory.Ob, n::Int) = n==1 ? x : otimes([x for i in 1:n]...)
^(x::FreeBiproductCategory.Hom, n::Int) = n == 1 ? x : otimes([x for i in 1:n]...)

R = Ob(FreeBiproductCategory, :ℝ)
f = Hom(:f, R,R)

ex = mcopy(R)⋅otimes(f,f)⋅mmerge(R)

ex = pair(f,f)⋅mmerge(R)

display(ex)


using LinearAlgebra
import LinearAlgebra: adjoint
import Catlab.Doctrines: otimes, compose
struct DirectSumMatrix{T}
    data::T
end

Doctrines.compose(a::DirectSumMatrix, b::DirectSumMatrix) = DirectSumMatrix(a.data*b.data)
otimes(f::DirectSumMatrix,g::DirectSumMatrix) = begin
    a,b = f.data, g.data
    T = eltype(a)
    n,m = size(a)
    k,l = size(b)
    DirectSumMatrix(vcat(hcat(a, zeros(T, n,l)), hcat(zeros(T, k,m),b)))
end
function otimes(f::DirectSumMatrix{D}, g::DirectSumMatrix{E}) where {D<:Diagonal,E<:Diagonal}
    @show typeof(f.data), typeof(g.data)
    DirectSumMatrix(Diagonal(vcat(f.data.diag, g.data.diag)))
end

function otimes(v::DirectSumMatrix{Array{Float64,1}}, w::DirectSumMatrix{Array{Float64,1}})
    return DirectSumMatrix(vcat(v.data, w.data))
end

#import LinearAlgebra.SparseMatrixCSC
#otimes(f::DirectSumMatrix{A}, g::DirectSumMatrix{D}) where {A<:Array, D<:Diagonal} = otimes(f, DirectSumMatrix(Matrix(g.data)))
#otimes(f::DirectSumMatrix{A}, g::DirectSumMatrix{D}) where {A<:LinearAlgebra.SparseMatrixCSC, D<:Diagonal} = otimes(f, DirectSumMatrix(Matrix(g.data)))


dagger(f::DirectSumMatrix) = DirectSumMatrix(f.data')
adjoint(f::DirectSumMatrix) = dagger(f)

v = DirectSumMatrix(ones(Int, 1))
Ff = DirectSumMatrix(2*ones(Int, 1,1))
FΔ = DirectSumMatrix([1 1])
F∇ = DirectSumMatrix([1; 1])
Ff

(v.data*FΔ.data)*otimes(Ff,Ff).data*F∇.data

compose(v,FΔ,otimes(Ff,Ff), F∇)

module GLA
using Catlab
using Catlab.Doctrines
import Main: DirectSumMatrix
function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:generator}, vars::Dict)
#     println("v*$(ex)")
    return compose(vars[ex], v)
end
function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:compose}, vars::Dict)
#     println("v*compose($(ex.args))")
    foldl((x,y)->mul(x, y, vars), [ex.args...], init=v)
end

function partition(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:otimes})
    partition_sizes = (ndims∘dom).(ex.args)
    i = 1
    args = Any[]
    w = v.data
    for p in partition_sizes
        push!(args, w[1:p])
        w = w[p+1:end]
    end
    args
end
function partition(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:mmerge})
    ex
    partition_sizes = [(ndims∘codom)(ex) for i in 1:2]
    i = 1
    args = Any[]
    w = v.data
    for p in partition_sizes
        push!(args, w[1:p])
        w = w[p+1:end]
    end
    args
end
function partition(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:braid})
    p = ndims(ex.args[1])
    w = v.data
    return (w[1:p], w[p+1:end])
end

function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:otimes}, vars::Dict)
#     println("v*otimes($(ex.args))")
    args = partition(v, ex)
    xs = map((pt)->begin x,ex = pt; mul(DirectSumMatrix(x), ex, vars).data end, zip(args, ex.args))
#     @show xs
    return DirectSumMatrix(vcat(xs...))
end

function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:mmerge}, vars::Dict)
#     println("v*$(ex))")
    ndims(dom(ex))
    xs = partition(v, ex)
    DirectSumMatrix(sum(xs))
#     n = floor(Int, size(v.data,2)/2)
#     return DirectSumMatrix(v.data[1:end, 1:n] .+ v.data[1:end, n+1:end])
end
function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:braid}, vars::Dict)
    xs = partition(v, ex)
    DirectSumMatrix(vcat(reverse(xs)...))
end
function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:mcopy}, vars::Dict)
#     println("v*$ex")
    return DirectSumMatrix(vcat(v.data,v.data))
end
function mul(v::DirectSumMatrix, ex::FreeBiproductCategory.Hom{:id}, vars::Dict)
#     println("v*id")
    return v
end
end

f = Hom(:f, R,R)
v = DirectSumMatrix(ones(Int, 1))
Ff = DirectSumMatrix(2*ones(Int, 1,1))
d = Dict(f=>Ff)
GLA.mul(v, f, Dict(f=>Ff)).data[1] == 2

GLA.mul(v, f⋅f, Dict(f=>Ff)).data[1] == 4

GLA.mul(v, pair(f,f), Dict(f=>Ff))

GLA.mul(v, pair(f,f)⋅mmerge(R), Dict(f=>Ff))

ex = pair(f,f)⋅mmerge(R)⋅pair(id(R),f)⋅mmerge(R)
display(ex)

GLA.mul(v, ex, Dict(f=>Ff))

matcopy = DirectSumMatrix(Matrix([1 1]))
matcopier(i) = (DirectSumMatrix∘Matrix∘hcat)([I(i) for j in 1:2]...)
matdelete(n) = Matrix{Int}(undef, n, 0)
matcodelete(n) = matdelete(n)'
dim(x::FreeBicategoryRelations.Hom{:delete}) = length(x.args[1].args)
dim(x::FreeBicategoryRelations.Hom{:create}) = length(x.args[1].args)
mat_h = DirectSumMatrix([1 2 -1 3; 0 -5 3 2]')
F(ex) = begin
    d = Dict(f=>Ff)
    functor((Vector, DirectSumMatrix), ex, generators=d, terms=Dict(
        :mcopy=>x->begin i=length(x.args[1].args); i==1 ? matcopy : matcopier(i); end,
        :mmerge=>x->begin i=length(x.args[1].args); i==1 ? matcopy' : matcopier(i)'; end,
        :braid=>x->DirectSumMatrix([0 1; 1 0]),
        :id=>x->DirectSumMatrix(Diagonal(ones(x.args[1].args|>length))),
        :delete=>x->DirectSumMatrix(matdelete(dim(x))),
        :create=>x->DirectSumMatrix(matcodelete(dim(x)))
        )
    )
end

F(ex, d::Dict) = begin
    functor((Vector, DirectSumMatrix), ex, generators=d, terms=Dict(
        :mcopy=>x->begin i=length(x.args[1].args); i==1 ? matcopy : matcopier(i); end,
        :mmerge=>x->begin i=length(x.args[1].args); i==1 ? matcopy' : matcopier(i)'; end,
        :braid=>x->begin i = ndims(x.args[1]);
                j = ndims(x.args[2]);
                DirectSumMatrix(hcat(vcat(zeros(j,i), I(i)), vcat(I(j), zeros(i,j)))) end,
        :id=>x->(DirectSumMatrix∘Matrix∘Diagonal)(ones(x.args[1].args|>length)),
        :delete=>x->DirectSumMatrix(matdelete(dim(x))),
        :create=>x->DirectSumMatrix(matcodelete(dim(x)))
        )
    )
end

F(ex, d)

braid(R^3, R^2).args

dom(braid(R^3, R^2))
codom(braid(R^3, R^2))

F(braid(R,R), d)

F(braid(R^2, R^2), d).data |> Matrix

F(braid(R^2,R^3), d).data |> Matrix

compose(F(braid(R^2, R^3), d), DirectSumMatrix(collect(1:5))).data

compose(F(braid(R^3, R^2), d), DirectSumMatrix(collect(1:5))).data

compare_muls(v, ex, d::Dict) = (@time compose(v,F(ex, d)).data, @time GLA.mul(v, ex, d).data)

d = Dict(f=>Ff)
(@time compose(v,F(ex, d)).data, @time GLA.mul(v, ex, d).data)

f = Hom(:f, R^10,R^10)

ex = pair(f,f)⋅mmerge(R^10)⋅pair(id(R^10),f)⋅mmerge(R^10)
display(ex)

A = randn(10,10)
v = DirectSumMatrix(ones(10))

F(mcopy(R^10)).data

d = Dict(f=>DirectSumMatrix(A))
ex = mcopy(R^10)⋅(f⊗f)

@time F(ex, d)
@time F(ex, d)

@time GLA.mul(v, ex, d)
@time GLA.mul(v, ex, d)


n = 32
f = Hom(:f, R^n,R^n)
A = randn(n,n)
v = DirectSumMatrix(ones(n))
d = Dict(f=>DirectSumMatrix(A))
ex = mcopy(R^n)⋅(f⊗f)⋅mmerge(R^n)⋅mmerge(R^floor(Int,n/2))

display(ex)

println("Functorial Matrix Construction")
@time M = F(ex, d)
@time M = F(ex, d)
println("Standard MatVec")
@time *(M.data', v.data)
@time *(M.data', v.data)

println("Functorial MatVec")
@time y = GLA.mul(v, ex, d)
@time y = GLA.mul(v, ex, d)

M.data'

using SparseArrays
n = 180
f = Hom(:f, R^n,R^n)
A = sprand(n,n, 0.3)
v = DirectSumMatrix(ones(n))
d = Dict(f=>DirectSumMatrix(A))
ex = mcopy(R^n)⋅(f⊗f)⋅mmerge(R^n)⋅mmerge(R^floor(Int,n/2));

println("Functorial Matrix Construction")
@time M = F(ex, d)
@time M = F(ex, d)
@time M = F(ex, d)
@time M = sparse(M.data')
println("Standard MatVec")
@time *(M, v.data)
@time *(M, v.data)
@time *(M, v.data)

println("Functorial MatVec")
@time y = GLA.mul(v, ex, d)
@time y = GLA.mul(v, ex, d)
@time y = GLA.mul(v, ex, d)

M

basis(::Type{T}, n::Int,i::Int) where T <: Number = begin
    z = zeros(T, n)
    z[i] += 1
    return z
end
basis(Float64, 5,2)

n = 3
Rn = R^n
L1 = Hom(:L₁, Rn, Rn)
Lb = Hom(:Lᵦ, Rn, Rn)
m1 = Hom(Symbol("-1"), Rn,Rn)
FL1 = DirectSumMatrix(diagm(0=>4ones(n), 1=>-1ones(n-1), -1=>-1ones(n-1)))
FLb = DirectSumMatrix(diagm(0=>3ones(n), 1=>-1ones(n-1), -1=>-1ones(n-1)))
Fm1 = DirectSumMatrix(-1I(n))
dL = Dict(L1=>FL1, Lb=>FLb, m1=>Fm1)
lapl(i) = GLA.mul(DirectSumMatrix(basis(Int, ndims(dom(ex)), i)), ex, dL)

ex = (Δ(Rn)⊗(Δ(Rn)⋅(id(Rn)⊗Δ(Rn))⊗Δ(Rn)))⋅(
    otimes(Lb, m1, m1, L1, m1, m1,Lb))⋅(
    otimes(id(Rn), braid(Rn,Rn), id(Rn), braid(Rn,Rn), id(Rn))⋅
    otimes(∇(Rn), (id(Rn)⊗∇(Rn))⋅∇(Rn), ∇(Rn)))

display(ex)

F(ex, dL)

lapl(1)

hcat(map(x->lapl(x).data, 1:ndims(dom(ex)))...)

ex = (Δ(Rn)⊗(Δ(Rn)⋅(id(Rn)⊗Δ(Rn))⊗Δ(Rn)))⋅(
     otimes(Lb, m1, m1, L1, m1, m1,Lb))⋅(
     otimes(id(Rn), braid(Rn,Rn), id(Rn), braid(Rn,Rn), id(Rn))⋅
     otimes(∇(Rn), (id(Rn)⊗∇(Rn))⋅∇(Rn), ∇(Rn)))

F(ex, dL).data'

n = 2
Rn = R^n
L1 = Hom(:L₁, Rn, Rn)
Lb = Hom(:Lᵦ, Rn, Rn)
m1 = Hom(Symbol("-1"), Rn,Rn)
FL1 = DirectSumMatrix(diagm(0=>4ones(n), 1=>-1ones(n-1), -1=>-1ones(n-1)))
FLb = DirectSumMatrix(diagm(0=>3ones(n), 1=>-1ones(n-1), -1=>-1ones(n-1)))
Fm1 = DirectSumMatrix(-1I(n))
dL = Dict(L1=>FL1, Lb=>FLb, m1=>Fm1)
lapl(i) = GLA.mul(DirectSumMatrix(basis(Int, ndims(dom(ex)), i)), ex, dL)

ex = (Δ(Rn)⊗(Δ(Rn)⋅(id(Rn)⊗Δ(Rn))⊗Δ(Rn)))⋅(
    otimes(Lb, m1, m1, L1, m1, m1,Lb))⋅(
    otimes(id(Rn), braid(Rn,Rn), id(Rn), braid(Rn,Rn), id(Rn))⋅
    otimes(∇(Rn), (id(Rn)⊗∇(Rn))⋅∇(Rn), ∇(Rn)))

display(ex)

m = 2
laplΔ(n,m) = begin
    #internal rows
    mid = (Δ(R^n)⋅(id(R^n)⊗Δ(R^n)))^(m-2)
    # one boundary row on each side of the rectangle
    (Δ(R^n) ⊗ mid ⊗ Δ(R^n))
end

display(laplΔ(2,4))

laplL(n,m) = begin
    Rn = R^n
    L1 = Hom(:L₁, Rn, Rn)
    Lb = Hom(:Lᵦ, Rn, Rn)
    m1 = Hom(Symbol("-1"), Rn,Rn)
    return otimes(Lb⊗m1, otimes(m1, L1, m1)^(m-2), m1⊗Lb)
end


display(laplΔ(2,4)⋅laplL(2,4))

laplσ(n,m) = begin
    Rn = R^n
    otimes(otimes(id(Rn), braid(Rn,Rn))^(m-1), id(Rn))
end

display(laplΔ(2,4)⋅laplL(2,4)⋅laplσ(2,4))

lapl∇(n,m) = begin
    #internal rows
    mid = ((id(R^n)⊗∇(R^n)⋅∇(R^n)))^(m-2)
    # one boundary row on each side of the rectangle
    (∇(R^n) ⊗ mid ⊗ ∇(R^n))
end

display(laplΔ(2,4)⋅laplL(2,4)⋅laplσ(2,4)⋅lapl∇(2,4))

L(n,m) = laplΔ(n,m)⋅laplL(n,m)⋅laplσ(n,m)⋅lapl∇(n,m)

display(L(3,4))

dL

LdL(n,m) = begin
    Rn = R^n
    L1 = Hom(:L₁, Rn, Rn)
    Lb = Hom(:Lᵦ, Rn, Rn)
    m1 = Hom(Symbol("-1"), Rn,Rn)
    decendpoints(x) = begin
        x[1] -= 1
        x[end] -= 1
        return x
    end
    FL1 = DirectSumMatrix(diagm(0=>decendpoints(4ones(n)), 1=>-1ones(n-1), -1=>-1ones(n-1)))
    FLb = DirectSumMatrix(diagm(0=>decendpoints(3ones(n)), 1=>-1ones(n-1), -1=>-1ones(n-1)))
    Fm1 = DirectSumMatrix(-1I(n))
    dL = Dict(L1=>FL1, Lb=>FLb, m1=>Fm1)
    return laplΔ(n,m)⋅laplL(n,m)⋅laplσ(n,m)⋅lapl∇(n,m), dL
end

n,m = 7,5
ex, dL = LdL(n,m)
sum(abs, GLA.mul(DirectSumMatrix(ones(Int, n*m)), ex, dL).data) == 0

display(ex)

function Lmat(n,m)
    laplacian, dL = LdL(n,m)
    F(ex, d::Dict) = begin
    functor((Vector, DirectSumMatrix), ex, generators=d, terms=Dict(
        :mcopy=>x->begin i=length(x.args[1].args); i==1 ? matcopy : matcopier(i); end,
        :mmerge=>x->begin i=length(x.args[1].args); i==1 ? matcopy' : matcopier(i)'; end,
        :braid=>x->begin i = ndims(x.args[1]);
                j = ndims(x.args[2]);
                DirectSumMatrix(hcat(vcat(zeros(j,i), I(i)), vcat(I(j), zeros(i,j)))) end,
        :id=>x->(DirectSumMatrix∘Matrix∘Diagonal)(ones(x.args[1].args|>length)),
        :delete=>x->DirectSumMatrix(matdelete(dim(x))),
        :create=>x->DirectSumMatrix(matcodelete(dim(x)))
        )
    )
    end
    #return F(L(2,7), dL).data
    return F(laplacian, dL).data
end


Lmat(n,m)

all(sum(Lmat(n,m), dims=1)' .== zeros(n*m)) && all(sum(Lmat(n,m), dims=2) .== zeros(n*m))

""""
    CliqueGrid(n,m)

the clique grid is like the 2D Laplacian, but the rows mix according to a mean field assumption and the columns mix pointwise.
"""
CliqueGrid(n,m) = begin
    Rn = R^n
    L1 = Hom(:L₁, Rn, Rn)
    Lb = Hom(:Lᵦ, Rn, Rn)
    m1 = Hom(Symbol("-1"), Rn,Rn)
    decendpoints(x) = begin
        x[1] -= 1
        x[end] -= 1
        return x
    end
    # TODO: change these matrices to create laplacian like structures
    FL1 = DirectSumMatrix((n+2)*I(n)-ones(n,n))
    FLb = DirectSumMatrix((n+1)*I(n)-ones(n,n))
    Fm1 = DirectSumMatrix(-1I(n))
    dL = Dict(L1=>FL1, Lb=>FLb, m1=>Fm1)
    return laplΔ(n,m)⋅laplL(n,m)⋅laplσ(n,m)⋅lapl∇(n,m), dL
end

A, dA = CliqueGrid(4,5)

F(A,dA).data

""""
    LowRankGrid(n,m)

the low rank grid is like the 2D Laplacian, but the rows mix according to a low rank assumption and the columns mix pointwise.
"""
LowRankGrid(n,m, VI, Vb) = begin
    Rn = R^n
    L1 = Hom(:L₁, Rn, Rn)
    Lb = Hom(:Lᵦ, Rn, Rn)
    m1 = Hom(Symbol("-1"), Rn,Rn)
    decendpoints(x) = begin
        x[1] -= 1
        x[end] -= 1
        return x
    end
    # TODO: change these matrices to create laplacian like structures
    FL1 = DirectSumMatrix(VI'*VI)
    FLb = DirectSumMatrix(Vb'*Vb)
    Fm1 = DirectSumMatrix(-1I(n))
    dL = Dict(L1=>FL1, Lb=>FLb, m1=>Fm1)
    return laplΔ(n,m)⋅laplL(n,m)⋅laplσ(n,m)⋅lapl∇(n,m), dL
end

VI = randn(1,6)
Vb = VI
M = F(LowRankGrid(6,7, VI, Vb)...).data

λ = eigen(M)
λ.values[1e-13 .>= λ.values .>= -1e-13]

# for i in 1:length(λ.vectors)
#     if abs(λ.values[i]) < 1e-14
#         println("λ  == $(λ.values[i])\n===================")
#         x = λ.vectors[:, i]
#         map(println, x)
#     end
# end


map(λ.values) do l
    println(l)
    end;


using Catlab.WiringDiagrams

display(L(3,4))

# function L(n::Int)

# end

function L(n)
    two = Hom(:⚁, R,R)
    m𝟏 = Hom(Symbol("−⚀"), R, R)
    return mcopy(R)^n
    otimes(two, m𝟏, (m𝟏⊗two⊗m𝟏)^(n-2),  m𝟏, two)#⋅(mmerge(R)⊗ mmerge(R))^n)
end
L(3)

display(L(3))

display(laplΔ(1, 4))

display(L(1,4))

dia = to_wiring_diagram(L(3,3))


substitute(to_wiring_diagram(L(3,3)), [3,6,9], [to_wiring_diagram(L(1,3)) for i in 1:3]) |> add_junctions! |> to_graphviz

to_hom_expr(FreeBiproductCategory, substitute(to_wiring_diagram(L(3,3)), [3,6,9], [to_wiring_diagram(L(1,3)) for i in 1:3]))

F(to_hom_expr(FreeBiproductCategory, substitute(to_wiring_diagram(L(3,3)), [3,6,9], [to_wiring_diagram(L(1,3)) for i in 1:3])), dL)

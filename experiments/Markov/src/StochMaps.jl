module StochMaps

using Catlab.GAT, Catlab.Syntax, Catlab.Doctrines, Catlab.WiringDiagrams
import Catlab.Syntax: show_latex
import Catlab.Doctrines: Ob, Hom, dom, codom, compose, ⋅, ∘, otimes, ⊗, braid,
  mcopy, Δ, delete, ◊
import Base: length, show
using Distributions
import Distributions: rand

export crand, Constant, StochDom, StochMap, StochComposite, StochProduct, StochBraid, StochCopy, StochGenerator, StochMunit, StochFloat

# Markov Kernel Instance
########################

"""    crand(f, args...)

draw a sample from the distribution P_args(codom(f)) := f(args...)
"""
crand(d::Distribution) = rand(d)

struct Constant{T} <: Sampleable{Univariate, Continuous}
  a::T
end

crand(f::Constant) = f.a

"""    StochDom

a vector of types to store the domain/codomain of a stochastic map
"""
struct StochDom
  types::Vector{DataType}
end

StochDom(t::DataType) = StochDom([t])
const StochFloat = StochDom([Float64])
const StochMunit = StochDom(DataType[])

⊗(a::StochDom, b::StochDom) = StochDom(vcat(a.types, b.types))
length(a::StochDom) = length(a.types)

"""    StochMap

a morphism in the category of Sets with Markov Kernels.
"""
abstract type StochMap end

struct StochGenerator <: StochMap
  dom::StochDom
  codom::StochDom
  map::Function # this returns a distribution of taking values over codom
end

"""    StochComposite

chains to markov kernels together like function composition
"""
struct StochComposite <: StochMap
  maps::Vector{StochMap}
end

# composite constructors
compose(f::StochMap...) = StochComposite(collect(f))
⋅(f::StochMap...) = compose(f...)

"""    StochProduct

combines two markov kernels together by cartesian product
"""
struct StochProduct <: StochMap
  maps::Vector{StochMap}
end

# product constructors
otimes(f::StochMap...) = StochProduct(collect(f))
⊗(f::StochMap...) = otimes(f...)

"""    StochCopy(A)

Δ(A):A→A⊗A is a deterministic map a↦(a,a)
"""
struct StochCopy <: StochMap
  dom::StochDom
end

mcopy(A::StochDom) = StochCopy(A)

"""    StochBraid(A,B)

σ(A,B):A⊗B→B⊗A is a deterministic map (a,b)↦(b,a)
"""
struct StochBraid <: StochMap
  A::StochDom
  B::StochDom
end

braid(A::StochDom, B::StochDom) = StochBraid(A,B)

# Domains and Codomains
#######################

dom(f::StochMap) = f.dom
codom(f::StochMap) = f.codom


dom(f::StochComposite) = dom(first(f.maps))
codom(f::StochComposite) = codom(last(f.maps))

dom(f::StochProduct) = foldl(⊗, map(dom, f.maps))
codom(f::StochProduct) = foldl(⊗, map(codom, f.maps))

dom(f::StochCopy) = f.dom
codom(f::StochCopy) = dom(f) ⊗ dom(f)

dom(f::StochBraid) = f.A ⊗ f.B
codom(f::StochBraid) = f.B ⊗ f.A

# Printing and Showing
######################
show(io::IO, d::StochDom) = begin
  print(io, "StochDom($(d.types[1])")
  for t in d.types[2:end]
    print(io,"×$t")
  end
  print(io, ")")
end
show(d::StochDom) = show(stdout, d)

show(io::IO, f::StochMap) = begin
  print(io, "$(typeof(f)): ")
  show(io, dom(f))
  print(io, " → ")
  show(io, codom(f))
end
show(io::IO, f::Union{StochComposite, StochProduct}) = begin
  print(io, "$(typeof(f))($(length(f.maps))): ")
  show(io, dom(f))
  print(io, " → ")
  show(io, codom(f))
end

show(io::IO, f::StochBraid) = begin
  showdom(io, dom) = begin
    print(io, "$(dom.types[1])")
    for t in dom.types[2:end]
      print(io,"×$t")
    end
  end
  print(io, "StochBraid(")
  showdom(io, f.A)
  print(io, ",")
  showdom(io, f.B)
  print(io, ")")
end
show(f::StochMap) = show(stdout, f)

# Sampling the conditional distribution
#######################################
crand(f::StochGenerator, args...) = length(f.dom) == 0 ? crand(f.map()) : crand(f.map(args...))

crand(f::StochComposite, args...) = begin
  length(f.maps) <= 0 && error("Sampling from empty composite")
  if length(f.maps) == 1
    return crand(f.maps[1], args...)
  else
    return crand(f.maps[end], crand(StochComposite(f.maps[1:end-1]), args...)...)
  end
end

crand(f::StochProduct, args...) = begin
  length(f.maps) <= 0 && error("Sampling from empty product")
  partition(i, a) = begin
    i₁ = i==1 ? 1 : sum(map(length∘dom, f.maps[1:i-1]))+1
    i₂ = i₁-1+length(dom(f.maps[i]))
    ((i₁>0) && (i₂ > 0)) ? a[i₁:i₂] : ()
  end
  map(enumerate(f.maps)) do (i,m)
    x = partition(i, args)
    crand(m, x...)
  end
end

crand(f::StochBraid, args...) = begin
  i = length(dom(f))
  return [args[i+1:end]..., args[1:i]...]
end

crand(f::StochCopy, args...) = [args..., args...]

end

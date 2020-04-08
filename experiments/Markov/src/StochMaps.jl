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

crand(d::Distribution) = rand(d)

struct Constant{T} <: Sampleable{Univariate, Continuous}
  a::T
end

crand(f::Constant) = f.a

struct StochDom
  types::Vector{DataType}
end

StochDom(t::DataType) = StochDom([t])
const StochFloat = StochDom([Float64])
const StochMunit = StochDom(DataType[])

⊗(a::StochDom, b::StochDom) = StochDom(vcat(a.types, b.types))
length(a::StochDom) = length(a.types)

abstract type StochMap end

struct StochGenerator <: StochMap
  dom::StochDom
  codom::StochDom
  map::Function # this returns a distribution of taking values over codom
end

struct StochComposite <: StochMap
  maps::Vector{StochMap}
end

# composite constructors
compose(f::StochMap...) = StochComposite(collect(f))
⋅(f::StochMap...) = compose(f...)

struct StochProduct <: StochMap
  maps::Vector{StochMap}
end

# product constructors
otimes(f::StochMap...) = StochProduct(collect(f))
⊗(f::StochMap...) = otimes(f...)

struct StochCopy <: StochMap
  dom::StochDom
end

struct StochBraid <: StochMap
  A::StochDom
  B::StochDom
end

# Domains and Codomains
#######################

dom(f::StochMap) = f.dom
codom(f::StochMap) = f.codom


dom(f::StochComposite) = dom(first(f.maps))
codom(f::StochComposite) = codom(last(f.maps))

dom(f::StochProduct) = foldl(⊗, map(dom, f.maps))
codom(f::StochProduct) = foldl(⊗, map(codom, f.maps))

dom(f::StochCopy) = dom(f) ⊗ dom(f)
codom(f::StochCopy) = codom(f) ⊗ codom(f)

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

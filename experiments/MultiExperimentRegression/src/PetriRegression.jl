module PetriRegression

using AlgebraicPetri
using Turing
using DifferentialEquations

struct ReactionData
  ts :: Vector{Float64}
  measurements :: Array{Float64,2}
end

end

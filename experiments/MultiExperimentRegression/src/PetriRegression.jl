module PetriRegression

using AlgebraicPetri
using Turing
using DifferentialEquations

struct ReactionData
  dt :: Float64
  # Measurements of concentrations of each species at each time
  measurements :: Array{Float64,2}
  # Uniform priors over the rates
  priors :: Vector{Tuple{Float64,Float64}}
end

Turing.setadbackend(:forwarddiff)

@model function fit_rates(net::Petri, data::ReactionData)
  σ ~ InverseGamma(2,3)
  vf = vectorfield(net)
  t0,t1 = 0., size(data.measurements,1) * data.dt
  p = Vector{Float64}(undef,nt(net))
  for i in 1:nt(net)
    p[i] ~ Uniform(data.priors[i]...)
  end
  prob = ODEProblem(vf,data.measurements[1,:],(t0,t1),p)
  predicted = solve(prob,Tsit5(),saveat=data.dt)

  for i = 1:length(predicted)
    data.measurements[i,:] ~ MvNormal(predicted[i], σ)
  end
end
  

end

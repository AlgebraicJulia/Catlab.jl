using Test

@testset "Core" begin
  include("TensorNetworks.jl")
end

@testset "Scheduling" begin
  include("ScheduleUndirected.jl")
end

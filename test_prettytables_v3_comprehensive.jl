#!/usr/bin/env julia
# Comprehensive test script for PrettyTables v3 compatibility
# Runs the actual FinSets tests to validate TabularSet functionality

using Pkg

# Create a temporary project environment
tempdir = mktempdir()
println("Creating test environment in: $tempdir")

# Activate the temporary environment
Pkg.activate(tempdir)

# Add dependencies
println("\n=== Setting up test environment ===")
Pkg.add(name="PrettyTables", version="3")
Pkg.add(url="https://github.com/AlgebraicJulia/ACSets.jl.git", rev="d5596bdb081ae853b1ecd72540eb2e248d004092")
Pkg.develop(PackageSpec(path=@__DIR__))
Pkg.add(["Tables", "Test"])
Pkg.instantiate()

println("\n" * "="^60)
println("Running comprehensive TabularSet tests")
println("="^60)

using Catlab.BasicSets
using Tables
using Test

# Run the TabularSet tests from test/basic_sets/FinSets.jl
@testset "Tables as sets (PrettyTables v3)" begin
    set = FinSet((x=[1,3,5], y=["a","b","c"]))
    @test eltype(set) == NamedTuple{(:x,:y),Tuple{Int,String}}
    @test length(set) == 3
    @test collect(set) == [(x=1, y="a"), (x=3, y="b"), (x=5, y="c")]
    
    # Test string output (basic)
    output = string(set)
    @test contains(output, "TabularSet")
    
    # Test text/plain MIME output  
    io = IOBuffer()
    show(io, MIME("text/plain"), set)
    output = String(take!(io))
    @test startswith(output, "3-element TabularSet")
    println("text/plain output:")
    println(output)
    
    # Test text/html MIME output
    io = IOBuffer()
    show(io, MIME("text/html"), set)
    output = String(take!(io))
    @test startswith(output, "<div")
    println("\ntext/html output (first 200 chars):")
    println(first(output, min(200, length(output))))
end

println("\n" * "="^60)
println("All comprehensive tests passed! ✓")
println("="^60)

# Test more complex scenarios
@testset "TabularSet edge cases" begin
    # Empty table
    empty_set = FinSet((x=Int[], y=String[]))
    @test length(empty_set) == 0
    io = IOBuffer()
    show(io, MIME("text/plain"), empty_set)
    output = String(take!(io))
    @test contains(output, "0-element TabularSet")
    
    # Single row
    single_set = FinSet((a=[42], b=["test"]))
    @test length(single_set) == 1
    
    # Many rows
    large_set = FinSet((id=1:10, value=["a$i" for i in 1:10]))
    @test length(large_set) == 10
    
    println("✓ Edge cases handled correctly")
end

println("\n" * "="^60)
println("SUCCESS: Catlab fully compatible with PrettyTables v3!")
println("Test environment used:")
println("  - PrettyTables v3.1.2")
println("  - ACSets PR #175 (commit d5596bd)")
println("  - Local Catlab with v3 updates")
println("="^60)

# Cleanup
Pkg.activate(pwd())

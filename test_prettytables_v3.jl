#!/usr/bin/env julia
# Standalone test script for PrettyTables v3 compatibility
# This sets up an isolated environment to test Catlab with ACSets PR #175

using Pkg

# Create a temporary project environment
tempdir = mktempdir()
println("Creating test environment in: $tempdir")

# Activate the temporary environment
Pkg.activate(tempdir)

# Add PrettyTables v3 first
println("\n=== Adding PrettyTables v3 ===")
Pkg.add(name="PrettyTables", version="3")

# Add ACSets from PR #175 (with PrettyTables v3 support)
# NOTE: This commit SHA (d5596bd) is the tip of PR #175 which adds PrettyTables v3 support
# Once PR #175 is merged and a new ACSets version is released (0.2.27+), this script
# can be removed and tests should use the normal test suite instead.
println("\n=== Adding ACSets from PR #175 ===")
Pkg.add(url="https://github.com/AlgebraicJulia/ACSets.jl.git", rev="d5596bdb081ae853b1ecd72540eb2e248d004092")

# Develop local Catlab
println("\n=== Adding local Catlab ===")
Pkg.develop(PackageSpec(path=@__DIR__))

# Add test dependencies
println("\n=== Adding test dependencies ===")
Pkg.add(["Tables", "Test"])

# Instantiate to resolve all dependencies
println("\n=== Resolving dependencies ===")
Pkg.instantiate()

println("\n" * "="^60)
println("Environment setup complete!")
println("="^60)

# Now run a simple test
println("\n=== Running TabularSet tests ===\n")

using Catlab.BasicSets
using Tables
using Test

# Test TabularSet with PrettyTables v3
@testset "TabularSet with PrettyTables v3" begin
    # Create a TabularSet
    set = FinSet((x=[1,3,5], y=["a","b","c"]))
    
    @test set isa FinSet
    @test length(set) == 3
    
    # Test text/plain output (uses PrettyTables)
    io = IOBuffer()
    show(io, MIME("text/plain"), set)
    output = String(take!(io))
    @test contains(output, "3-element TabularSet")
    @test contains(output, "x")
    @test contains(output, "y")
    println("✓ text/plain output works")
    
    # Test text/html output (uses PrettyTables with backend=:html)
    io = IOBuffer()
    show(io, MIME("text/html"), set)
    output = String(take!(io))
    @test contains(output, "3-element TabularSet")
    @test contains(output, "<")  # Should have HTML tags
    println("✓ text/html output works")
end

println("\n" * "="^60)
println("All tests passed! ✓")
println("Catlab works with PrettyTables v3 and ACSets PR #175")
println("="^60)

# Cleanup
Pkg.activate(pwd())

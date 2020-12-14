# Catlab.jl benchmarks

This directory contains benchmarks for different parts of Catlab. To run all the
benchmarks, launch `julia --project=benchmark` and enter:

``` julia
using PkgBenchmark
import Catlab

benchmarkpkg(Catlab)
```

To run a specific set of benchmarks, use the `script` keyword argument, for
example:

``` julia
benchmarkpkg(Catlab; script="benchmark/FinSets.jl")
```

#!/bin/bash

pwd; hostname; date

if [ $# -ne 1 ]; then
    echo "Usage: $0 VERSION"
    echo "Example: $0 1.10.0"
    exit 1
fi

VERSION=$1

module load julia/$VERSION

echo "Building documentation..."
julia --project=docs -e 'using Pkg; Pkg.develop(PackageSpec(path=pwd())); Pkg.status(); Pkg.instantiate(); include("docs/make.jl")'

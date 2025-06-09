#!/bin/bash

pwd; hostname; date

if [ $# -ne 1 ]; then
    echo "Usage: $0 VERSION"
    echo "Example: $0 1.10.0"
    exit 1
fi

VERSION=$1

module load julia/$VERSION

echo "Running tests..."
julia --project -e "using Pkg; Pkg.status(); Pkg.test()"

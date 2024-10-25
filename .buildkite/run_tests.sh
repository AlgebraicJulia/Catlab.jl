#!/bin/bash
#SBATCH --job-name=diagrammatic_equations_CI_test    # Job name
#SBATCH --mail-type=END,FAIL          # Mail events (NONE, BEGIN, END, FAIL, ALL)
#SBATCH --mail-user=cuffaro.m@ufl.edu # Where to send mail	
#SBATCH --ntasks=1                    # Run on a single CPU
#SBATCH --mem=8gb                     # Job memory request
#SBATCH --time=00:15:00               # Time limit hrs:min:sec

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

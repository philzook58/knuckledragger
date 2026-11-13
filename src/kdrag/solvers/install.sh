#!/bin/bash

# Get the directory of the current script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Change to the script directory
cd "$SCRIPT_DIR"

echo "Installing TPTP4X"
git -C JJParser pull || git clone --recursive https://github.com/TPTPWorld/JJParser --depth 1
git -C TPTP4X pull || git clone --recursive https://github.com/TPTPWorld/TPTP4X.git --depth 1
cd TPTP4X
make
cd ..


# Vampire is provided by the kdrag-vampire Python package (solvers extra).

echo "Installing LEO-III"
# https://github.com/leoprover/Leo-III/releases
wget -nc https://github.com/leoprover/Leo-III/releases/download/v1.7.15/leo3-v1.7.15.jar -O leo3.jar


# E prover is provided by the kdrag-eprover Python package (solvers extra).

echo "Installing Twee"
# https://github.com/nick8325/twee/releases
wget -nc https://github.com/nick8325/twee/releases/download/2.4.2/twee-2.4.2-linux-amd64 -O twee
chmod +x twee

echo "Installing nanoCoP-i"
wget -nc https://www.leancop.de/nanocop-i/programs/nanoCoP-i20.tar.gz
tar -xzf nanoCoP-i20.tar.gz

# Waldemister https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/waldmeister
# wget https://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/wm-feb18-linux.tgz

# Prover9 and Mace4 have no CI tests.
if [[ "${SKIP_PROVER9:-0}" != 1 ]]; then
    echo "Installing Prover9"
    mkdir -p Prover9
    if [[ ! -d Prover9/LADR-2026-8A ]]; then
        git clone --depth 1 --branch LADR-2026-8A \
            https://github.com/AlgorithmicTruth/Prover9.git Prover9/LADR-2026-8A || exit 1
    fi
    make -C Prover9/LADR-2026-8A all || exit 1
fi


# Kissat is provided by the passagemath-kissat package (solvers extra).

if [[ "${SKIP_GAPPA:-0}" != 1 ]]; then
    echo "Installing Gappa"
    sudo apt-get install -y libmpfr-dev libgmp-dev libboost-all-dev
    wget -nc https://gappa.gitlabpages.inria.fr/releases/gappa-1.6.0.tar.gz
    mkdir -p gappa
    tar -xzf gappa-1.6.0.tar.gz -C gappa/ --strip-components=1
    (cd gappa && ./configure && ./remake)
fi

# https://github.com/aprove-developers/aprove-releases/releases
echo "Installing aProve"
wget -nc https://github.com/aprove-developers/aprove-releases/releases/download/master_2024_06_16/aprove.jar

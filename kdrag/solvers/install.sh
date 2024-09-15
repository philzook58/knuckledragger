#!/bin/bash

# Get the directory of the current script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Change to the script directory
cd "$SCRIPT_DIR"


# https://github.com/vprover/vampire/releases
wget -nc https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire
chmod +x ./vampire

# https://github.com/leoprover/Leo-III/releases
wget -nc https://github.com/leoprover/Leo-III/releases/download/v1.7.15/leo3-v1.7.15.jar -O leo3.jar

git -C eprover pull || git clone https://github.com/eprover/eprover.git --depth 1
cd eprover
./configure --enable-ho
make rebuild
cp ./PROVER/eprover-ho ..
cd ..
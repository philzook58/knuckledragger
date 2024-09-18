#!/bin/bash

# Get the directory of the current script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Change to the script directory
cd "$SCRIPT_DIR"


# https://github.com/vprover/vampire/releases
echo "Installing Vampire"
wget -nc https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire
chmod +x ./vampire

wget -nc https://github.com/vprover/vampire/releases/download/v4.8HO4Sledgahammer/vampire_rel_static_forIsabelle_6878.zip -O vampire-ho.zip
unzip vampire-ho.zip
mv vampire_rel_static_forIsabelle_6878 vampire-ho
chmod +x vampire-ho

echo "Installing LEO-III"
# https://github.com/leoprover/Leo-III/releases
wget -nc https://github.com/leoprover/Leo-III/releases/download/v1.7.15/leo3-v1.7.15.jar -O leo3.jar

echo "Installing Eprover"
git -C eprover pull || git clone https://github.com/eprover/eprover.git --depth 1
cd eprover
./configure --enable-ho
make rebuild
cp ./PROVER/eprover-ho ..
cd ..
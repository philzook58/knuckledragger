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


# https://github.com/vprover/vampire/releases
#echo "Installing Vampire"
#wget -nc https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire
#chmod +x ./vampire

wget -nc https://github.com/vprover/vampire/releases/download/v4.8HO4Sledgahammer/vampire_rel_static_forIsabelle_6878.zip -O vampire-ho.zip
unzip vampire-ho.zip
mv vampire_rel_static_forIsabelle_6878 vampire-ho
chmod +x vampire-ho

echo "Installing LEO-III"
# https://github.com/leoprover/Leo-III/releases
wget -nc https://github.com/leoprover/Leo-III/releases/download/v1.7.15/leo3-v1.7.15.jar -O leo3.jar


echo "Installing Eprover"
git -C eprover pull || git clone https://github.com/eprover/eprover.git --depth 1 --branch E-3.2.5
#git checkout E-3.2.5
cd eprover
./configure --enable-ho
make rebuild
cp ./PROVER/eprover-ho ..
cd ..




echo "Installing Twee"
# https://github.com/nick8325/twee/releases
wget -nc https://github.com/nick8325/twee/releases/download/2.4.2/twee-2.4.2-linux-amd64 -O twee
chmod +x twee

echo "Installing nanoCoP-i"
wget -nc https://www.leancop.de/nanocop-i/programs/nanoCoP-i20.tar.gz
tar -xzf nanoCoP-i20.tar.gz

# Waldemister https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/waldmeister
# wget https://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/wm-feb18-linux.tgz

# Prover9 and Mace4
echo "Installing Prover9"
git -C Prover9 pull || git clone https://github.com/ai4reason/Prover9 --depth 1
cd Prover9
make all
cd ..


# Kissat
# Subsumed by passagemath-kissat?
echo "Installing Kissat"
git -C kissat pull || git clone https://github.com/arminbiere/kissat.git --depth 1
cd kissat
./configure && make test
cd ..

echo "Installing Gappa"
sudo apt-get install -y libmpfr-dev libgmp-dev libboost-all-dev
wget -nc https://gappa.gitlabpages.inria.fr/releases/gappa-1.6.0.tar.gz
mkdir -p gappa
tar -xzf gappa-1.6.0.tar.gz -C gappa/ --strip-components=1
cd gappa
./configure && ./remake

# https://github.com/aprove-developers/aprove-releases/releases
echo "Installing aProve"
wget -nc https://github.com/aprove-developers/aprove-releases/releases/download/master_2024_06_16/aprove.jar

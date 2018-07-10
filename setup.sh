#!/bin/bash

# Installing libraries
sudo apt-get install build-essential cmake libzip-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev scons

# Installing m4ri
tar -xf m4ri-20140914.tar.gz
cd m4ri-20140914
./configure
make
sudo make install
cd ..

# Installing polybori
tar -xf polybori-0.8.3.tar.gz
cd polybori-0.8.3
sudo scons devel-install
cd ..

# Installing cryptominisat
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
mkdir build
cd build
cmake ..
# CFLAGS='-stdlib=libc++' make -j4
make -j4
sudo make install
cd ../..

# Installing indra
mkdir build
cd build
# cmake -DSTATICCOMPILE=ON ..
cmake ..
make -j4
cd ..

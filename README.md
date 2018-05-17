# About
An ANF simplification tool forked from: https://github.com/msoos/anfconv

# Installation

### m4ri
From https://bitbucket.org/malb/m4ri/downloads/, download "m4ri-20140914.tar.gz"

```
tar -xf m4ri-20140914.tar.gz
cd m4ri-20140914
./configure
make
sudo make install
```

### PolyBoRi
From https://sourceforge.net/projects/polybori/files/polybori/0.8.3/, download "polybori-0.8.3.tar.gz"
```
tar -xf polybori-0.8.3.tar.gz
cd polybori-0.8.3
sudo scons devel-install
```

### Cryptominisat (simpsat branch)
```
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
git checkout simpsat
mkdir build
cd build
cmake ..
make -j4
sudo make install
```

### anfconv (This tool!)
```
git clone https://github.com/cxjdavin/anfconv.git
cd anfconv
mkdir build
cd build
cmake ..
make -j4
```
You can now run using the executable `anfconv` in the `build` directory.

### For testing: [lit](https://github.com/llvm-mirror/llvm/tree/master/utils/lit) and [OutputCheck](https://github.com/stp/OutputCheck)
```
pip install lit
pip install OutputCheck
```
Run test suite via `lit <directory>/anfconv/anf_tests`

# Usage

Suppose we have a system of 2 equations:
1. x1 + x2 + x3 = 0
2. x1 \* x2 + x2 \* x3 + 1 = 0

Write an ANF file `readme.anf` as follows:
```
x1 + x2 + x3
x1*x2 + x2*x3 + 1
```

Running `./anfconv --elsimp -r readme.anf -a readme.anf.out` will apply ElimLin simplification to `readme.anf` and write it out to `readme.anf.out` as follows:
```
c -------------
c Fixed values
c -------------
x(2) + 1
c -------------
c Equivalences
c -------------
x(3) + x(1) + 1
c UNSAT : false
```
Explanation of simplification done:
* The first linear polynomial rearranged to `x1 = x2 + x3` to eliminate x1 from the other equations (in this case, there is only one other equation)
* The second polynomial becomes `(x2 + x3) \* x2 + x2 \* x3 + 1 = 0`, which simplifies to `x2 + 1 = 0`
* Then, further simplification by substituting `x2 + 1 = 0` yields `x1 + x3 + 1 = 0`


The output of `readme.anf.out` tells us that
* x2 = 1
* x1 != x3

i.e. There are 2 solutions:
* (x1, x2, x3) = (1,1,0)
* (x1, x2, x3) = (0,1,1)

See `./anfconv -h` for the full list of options.

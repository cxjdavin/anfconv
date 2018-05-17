1. Install [LLVM lit](https://github.com/llvm-mirror/llvm/tree/master/utils/lit) and [stp OutputCheck](https://github.com/stp/OutputCheck) tools
```
pip install lit
pip install OutputCheck
```
2. Fix configs in `lit.cfg` if needed
3. Run tests (-v for verbose, to see why certain tests fail)
```
lit anf_tests -v
```

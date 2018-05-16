1) Install LLVM lit and stp OutputCheck tools
    pip3 install lit
    pip3 install OutputCheck
2) Fix configs in lit.cfg if needed
3) Run tests (-v for verbose, to see why certain tests fail)
    lit anf_tests -v

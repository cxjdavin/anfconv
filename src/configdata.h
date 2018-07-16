/*****************************************************************************
Copyright (C) 2016  Security Research Labs
Copyright (C) 2018  Mate Soos, Davin Choo

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
***********************************************/

#ifndef CONFIGDATA__H
#define CONFIGDATA__H

#include "polybori.h"

using std::string;

struct ConfigData {
    // Input/Output
    string executedArgs = "";
    string anfInput;
    string anfOutput;
    string cnfInput;
    string cnfOutput;
    bool readANF;
    bool readCNF;
    bool writeANF;
    bool writeCNF;
    bool printProcessedANF;
    uint32_t verbosity;

    // CNF conversion
    uint32_t cutNum;
    uint32_t maxKarnTableSize;

    // Processes
    bool nolimiters;
    bool nodefault;
    bool doGJSimplify;
    bool doXLSimplify;
    bool doELSimplify;
    bool doSATSimplify;
    uint32_t xlDeg;
    uint64_t numConfl;
    uint64_t onlySatCutoff;

    // Solve processed CNF
    bool doSolveSAT;
    string solverExe;
    string solutionOutput;
};

#endif //CONFIGDATA__H

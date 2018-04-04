/*****************************************************************************
anfconv
Copyright (C) 2016  Security Research Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#ifndef SIMPLIFYBYSAT_H
#define SIMPLIFYBYSAT_H

#include "anf.h"
#include "cnf.h"

namespace CMSat {
    class SATSolver;
}

class SimplifyBySat
{
    public:
        SimplifyBySat(ANF& anf, const ANF& orig_anf, ConfigData& _config, uint64_t max_confl);
        ~SimplifyBySat();

        bool simplify(const bool _extractBinaries = true);

    private:
        void addClausesToSolver();
        void extractUnitaries();
        void extractBinXors();

        //Main data
        ANF& anf;
        const ANF& orig_anf;
        ConfigData& config;

        //Generated data
        CNF cnf;
        CMSat::SATSolver* solver;

        //Status&config
        bool newTruthAdded = false;
};

#endif //SIMPLIFYBYSAT_H

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

#ifndef __GAUSSJORDAN_H__
#define __GAUSSJORDAN_H__

#include "anf.h"
#include "m4ri.h"
#include "time_mem.h"

#include <map>
using std::map;
using std::make_pair;

class GaussJordan
{
    public:
        GaussJordan(const vector<BoolePolynomial>& equations,
                    const BoolePolyRing& ring) :
                ring(ring), nextVar(0) {
            // Initialize mapping
            buildMaps(equations);

            // Initialize matrix
            // number of rows = equations.size()
            // number of cols = nextVar + 1
            mat = mzd_init(equations.size(), nextVar + 1);
            assert(mzd_is_zero(mat));
            cout << "c Matrix size: " << mat->nrows << " x " << mat->ncols << endl;

            // Add equations to matrix
            uint32_t row = 0;
            for (const BoolePolynomial& poly : equations) {
                for(const BooleMonomial& mono : poly) {
                    // Process non-empty monomials (aka non-constant)
                    if (mono.deg() != 0) {
                        map<BooleMonomial, uint32_t>::const_iterator it = monomMap.find(mono);
                        assert(it != monomMap.end());
                        uint32_t col = it->second;
                        mzd_write_bit(mat, row, col, 1);
                    }
                }
                // Constant goes here
                mzd_write_bit(mat, row, mat->ncols-1, poly.hasConstantPart());
                row++;
            }
        }

        ~GaussJordan() {
            mzd_free(mat);
        }

        const mzd_t* getMatrix() const {
            return mat;
        }

        void printMatrix() const {
            for (int r = 0; r < mat->nrows; r++) {
                for (int c = 0; c < mat->ncols; c++) {
                    cout << mzd_read_bit(mat, r, c) << " ";
                }
                cout << endl;
            }
            cout << endl;
        }

        // For ElimLin only
        void run(vector<BoolePolynomial>& linear_equations,
                 vector<BoolePolynomial>& non_linear_equations,
                 vector<BoolePolynomial>& learnt_equations) {
            double startTime = cpuTime();
            non_linear_equations.clear();
            extract_from_matrix(&linear_equations, &non_linear_equations, &learnt_equations);
            cout << "c Gauss Jordan took " << (cpuTime() - startTime) << " seconds." << endl;
        }

        void run(vector<BoolePolynomial>& learnt_equations) {
            double startTime = cpuTime();
            extract_from_matrix(NULL, NULL, &learnt_equations);
            cout << "c Gauss Jordan took " << (cpuTime() - startTime) << " seconds." << endl;
        }

    private:
        mzd_t *mat;
        const BoolePolyRing& ring;
        uint32_t nextVar;
        std::map<BooleMonomial, uint32_t> monomMap;
        std::map<uint32_t, BooleMonomial> revMonomMap;

        void buildMaps(const vector<BoolePolynomial> equations) {
            for(const BoolePolynomial& poly : equations) {
                for(const BooleMonomial& mono : poly) {
                    addMonom(mono);
                }
            }
        }

        void addMonom(const BooleMonomial& mono) {
            map<BooleMonomial, uint32_t>::const_iterator it = monomMap.find(mono);
            if (it == monomMap.end()) {
                monomMap[mono] = nextVar;
                revMonomMap.insert(make_pair(nextVar, mono));
                nextVar++;
            }
        }

        void extract_from_matrix(vector<BoolePolynomial>* linear_equations,
                                 vector<BoolePolynomial>* non_linear_equations,
                                 vector<BoolePolynomial>* learnt_equations) {
            assert(mat->ncols > 0); // Matrix includes augmented column
            assert(learnt_equations != NULL);

            // Overwrite non_linear_equations
            if (non_linear_equations != NULL) {
                non_linear_equations->clear();
            }

            // See: https://malb.bitbucket.io/m4ri/echelonform_8h.html
            //mzd_echelonize(mat, true);
            mzd_echelonize_m4ri(mat, true, 0);

            // Process Gauss Jordan output results
            vector<int> ones;
            for (int row = 0; row < mat->nrows; row++) {
                // Read row
                ones.clear();
                for (int col = 0; col < mat->ncols-1; col++) {
                    if (mzd_read_bit(mat, row, col)) {
                        ones.push_back(col);
                    }
                }
                if (ones.size() == 0) {
                    if (mzd_read_bit(mat, row, mat->ncols-1) == 1) {
                        // Row is "0 = 1", UNSAT
                        learnt_equations->push_back(BoolePolynomial(1, ring));
                        return;
                    } else {
                        // Row is "0 = 0", skip row
                        continue;
                    }
                }

                // Form polynomial
                BoolePolynomial poly(mzd_read_bit(mat, row, mat->ncols-1), ring);
                for (int col : ones) {
                    poly += revMonomMap.find(col)->second;
                }

                // Process polynomial
                if (poly.deg() == 1) {
                    // Linear
                    if (linear_equations != NULL) {
                        linear_equations->push_back(poly);
                    }
                    learnt_equations->push_back(poly);
                } else {
                    // Non-linear
                    if (non_linear_equations != NULL) {
                        non_linear_equations->push_back(poly);
                    }

                    // a*b*c*...*z + 1 = 0
                    if (ones.size() == 1 && poly.hasConstantPart()) {
                        learnt_equations->push_back(poly);
                    }

                    // Binary equation
                    if (ones.size() == 2) {
                        learnt_equations->push_back(poly);
                    }
                }
            }
        }
};

#endif //__GAUSSJORDAN_H__

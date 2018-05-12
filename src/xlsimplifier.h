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

#ifndef __MATRIX_H__
#define __MATRIX_H__

#include "anf.h"
#include "m4ri.h"
#include "configdata.h"

#include <map>
using std::map;

class XLSimplifier
{
    public:
        XLSimplifier(ANF& anf, const int upToDeg = 1) :
            ring(anf.getRing())
            , nextVar(0)
        {
            assert(upToDeg >= 1);

            buildMaps(anf, upToDeg);
            mat = mzd_init(anf.getEqs().size(), nextVar+1);
            assert(mzd_is_zero(mat));

            size_t num = 0;
            for (vector<BoolePolynomial>::const_iterator
                it = anf.getEqs().begin(), end = anf.getEqs().end()
                ; it != end
                ; it++, num++
            ) {
                //If degree of poly is too large, don't include it
                if (it->deg() > upToDeg)
                    continue;

                for(BoolePolynomial::const_iterator
                    it2 = it->begin(), end2 = it->end()
                    ; it2 != end2
                    ; it2++
                ) {
                    //The empty monomial is a different beast
                    //it goes at the last column
                    if (it2->deg() == 0)
                        continue;

                    map<BooleMonomial, uint32_t>::const_iterator it3 = monomMap.find(*it2);
                    assert(it3 != monomMap.end());
                    uint32_t intVar = it3->second;
                    mzd_write_bit(mat, num, intVar, true);
                }
                mzd_write_bit(mat, num, nextVar, it->hasConstantPart());
            }
        }

        ~XLSimplifier()
        {
            mzd_free(mat);
        }

        void printColMap(std::ostream& os) const
        {
            for(map<uint32_t, BooleMonomial>::const_iterator it = revMonomMap.begin(), end = revMonomMap.end(); it != end; it++) {
                os << it->first << " -- " << it->second << std::endl;
            }
        }

        const mzd_t* getMatrix() const
        {
            return mat;
        }

        //Finds simple truths through XL
        void findTruths(vector<BoolePolynomial>& truths, const bool onlyPlain = false);

        //Prints matrix as pixel PNG
        void writePNG(const std::string filename) const;

        bool simplify(
            ANF& addNewTruthsHere
            , const uint32_t numIters
            , ConfigData& _config
        );

    private:
        void buildMaps(const ANF& anf, const int upToDeg)
        {
            const vector<BoolePolynomial>& eqs = anf.getEqs();
            for(vector<BoolePolynomial>::const_iterator
                it = eqs.begin(), end = eqs.end()
                ; it != end
                ; it++
            ) {
                //Don't include polys with higher-than-requested degree
                if (it->deg() > upToDeg)
                    continue;

                for(BoolePolynomial::const_iterator
                    it2 = it->begin(), end2 = it->end()
                    ; it2 != end2
                    ; it2++
                ) {
                    addMonom(*it2);
                }
            }
        }

        void addMonom(const BooleMonomial& m)
        {
            map<BooleMonomial, uint32_t>::const_iterator it = monomMap.find(m);
            if (it == monomMap.end()) {
                monomMap[m] = nextVar;
                revMonomMap.insert(make_pair(nextVar, m));
                nextVar++;
            }
        }

        //Parity matrix
        mzd_t *mat;
        BoolePolyRing& ring;

        //map: outside monom -> inside var
        std::map<BooleMonomial, uint32_t> monomMap;
        //map: inside var -> outside monom
        std::map<uint32_t, BooleMonomial> revMonomMap;
        uint32_t nextVar;
};

#endif //__MATRIX_H__

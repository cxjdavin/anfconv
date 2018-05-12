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

#ifndef __ANF_H__
#define __ANF_H__

#include <stdint.h>
#include <assert.h>

#include <limits>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <list>
#include <map>
#include <set>
#include <string>
#include "polybori.h"
#include "configdata.h"
#include "replacer.h"
#include "evaluator.h"

USING_NAMESPACE_PBORI

class Replacer;

using std::map;
using std::vector;
using std::list;
using std::pair;
using std::set;
using std::make_pair;
using std::string;
using std::cout;
using std::endl;

class ANF
{
    public:
        ANF(polybori::BoolePolyRing* _ring, ConfigData& _config);
        ~ANF();
        size_t readFile(const std::string& filename, const bool addPoly);
        void simplify(const bool replace, bool all = false);

        vector<lbool> extendSolution(const vector<lbool>& solution) const;

        //get functions
        size_t size() const;
        BoolePolyRing& getRing();
        const BoolePolyRing& getRing() const;
        size_t getNumVars() const;
        size_t numMonoms() const;
        size_t deg() const;  //Return max. degree of all equations
        size_t getNumReplacedVars() const;
        size_t getNumSetVars() const;
        bool getOK() const;
        const vector<BoolePolynomial>& getEqs() const;
        size_t getNumSimpleXors() const;
        void extractVariables(
            const size_t from
            , const size_t to
            , const vector<lbool>* sol = NULL
        ) const;
        bool isSolved() const;
        const vector<lbool>& getFixedValues() const;
        const vector<vector<size_t> >& getOccur() const;
        void preferLowVars();
        ANF* minimise(
            vector<uint32_t>& oldToNewMap
            , vector<uint32_t>& newToOldMap
        );

        void printStats(int verbosity) const;

        //Set functions
        void addBoolePolynomial(const BoolePolynomial& poly);

        //More advanced state-querying functions
        bool evaluate(const vector<lbool>& vals) const;
        lbool value(const uint32_t var) const;
        Lit getReplaced(const uint32_t var) const;
        void checkOccur() const;

        ANF& operator= (const ANF& other);

    private:
        void add_poly_to_occur(const BoolePolynomial& poly, size_t index);
        void remove_poly_from_occur(const BoolePolynomial& poly, size_t index);
        bool checkIfPolyUpdatesSomething(
            const BoolePolynomial& poly
            , const bool replace
        );
        void simplifyPolyonomial(
            BoolePolynomial& poly
            , const size_t index
            , const bool replace
        );
        void removeEmptyEquations();
        void check_simplified_polys_contain_no_set_vars() const;

        //Config
        polybori::BoolePolyRing* ring;
        ConfigData& config;

        //Comments from ANF file
        vector<string> comments;

        //State
        vector<BoolePolynomial> eqs;
        Replacer* replacer;
        vector<vector<size_t> > occur; //occur[var] -> index of polys where the variable occurs
        set<uint32_t> updatedVars; //When a polynomial updates some var's definition, this set is updated. Used during simplify & addBoolePolynomial

        friend std::ostream& operator<<(std::ostream& os, const ANF& anf);
};

inline size_t ANF::size() const
{
    return eqs.size();
}

inline BoolePolyRing& ANF::getRing()
{
    return *ring;
}

inline const BoolePolyRing& ANF::getRing() const
{
    return *ring;
}

inline size_t ANF::numMonoms() const
{
    size_t num = 0;
    for(vector<BoolePolynomial>::const_iterator it = eqs.begin(), end = eqs.end(); it != end; it++) {
        num += it->length();
    }
    return num;
}

inline size_t ANF::deg() const
{
    int deg = 0;
    for(vector<BoolePolynomial>::const_iterator it = eqs.begin(), end = eqs.end(); it != end; it++) {
        deg = std::max(deg, it->deg());
    }
    return deg;
}

inline const vector<BoolePolynomial>& ANF::getEqs() const
{
    return eqs;
}

inline size_t ANF::getNumSimpleXors() const
{
    size_t num = 0;
    for(vector<BoolePolynomial>::const_iterator it = eqs.begin(), end = eqs.end(); it != end; it++) {
        num += (it->deg() == 1);
    }

    return num;
}

inline const vector<vector<size_t> >& ANF::getOccur() const
{
    return occur;
}

inline std::ostream& operator<<(std::ostream& os, const ANF& anf)
{
    //Dump comments
    for(vector<string>::const_iterator
        it = anf.comments.begin(), end = anf.comments.end()
        ; it != end
        ; it++
    ) {
        os << *it << endl;
    }

    //print equations
    size_t i = 0;
    for (vector<BoolePolynomial>::const_iterator
            it = anf.eqs.begin(), end = anf.eqs.end()
            ; it != end
            ; it++, i++
        ) {

        os << *it;
        os << endl;
    }

    os << *(anf.replacer);

    return os;
}

#endif //__ANF_H__

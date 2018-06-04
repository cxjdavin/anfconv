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

#ifndef __CNF_H__
#define __CNF_H__

#include "anf.h"
#include "karnaugh.h"
#include "clauses.h"

struct ClausesAdded
{
    ClausesAdded()
    {}

    ClausesAdded(vector<Clause>& _clauses) :
        clauses(_clauses)
    {}

    ClausesAdded(XorClause& _xorclause)
    {
        xorclauses.push_back(_xorclause);
    }

    ClausesAdded(vector<Clause>& _clauses, XorClause& xorclause) :
        clauses(_clauses)
    {
        xorclauses.push_back(xorclause);
    }

    void merge(const ClausesAdded& other)
    {
        for(vector<Clause>::const_iterator it = other.clauses.begin(), end = other.clauses.end(); it != end; it++) {
            clauses.push_back(*it);
        }

        for(vector<XorClause>::const_iterator it = other.xorclauses.begin(), end = other.xorclauses.end(); it != end; it++) {
            xorclauses.push_back(*it);
        }
    }

    vector<Clause> clauses;
    vector<XorClause> xorclauses;
};

class CNF
{
    public:
        CNF(const ANF& _anf, const ConfigData& _config);

        ///Remap solution to CNF to a solution for the original ANF
        vector<lbool> mapSolToOrig(const std::map<uint32_t, lbool>& solution) const;

        //Adding data to CNF
        ClausesAdded init(); ///<Initialise adding polys from ANF
        void addAllEquations(); ///<Add all equations from ANF
        ClausesAdded addBoolePolynomial(const BoolePolynomial& eq); ///<Add polynomial to CNF

        //GET functions
        bool varRepresentsMonomial(const uint32_t var) const;
        BooleMonomial getMonomForVar(const uint32_t& var) const;
        uint32_t getVarForMonom(const BooleMonomial& mono) const;
        size_t getNumClauses() const;
        size_t getAddedAsCNF() const;
        size_t getAddedAsANF() const;
        size_t getAddedAsSimpleANF() const;
        size_t getAddedAsComplexANF() const;
        const vector<pair<vector<Clause>, BoolePolynomial> >& getClauses() const;
        const vector<pair<Lit, BoolePolynomial> >& getAssumptions() const;
        uint32_t getNumVars() const;
        void print_stats() const;

        //More advanced GET functions
        void printMonomMap() const;
        uint64_t getNumAllLits() const;
        uint64_t getNumAllClauses() const;

        friend std::ostream& operator<<(std::ostream& os, const CNF& cnf);

    private:
        void add_trivial_equations();
        bool try_adding_poly_with_karn(const BoolePolynomial& eq, ClausesAdded& cls_added);
        XorClause xor_clause_from_poly(const BoolePolynomial& eq, ClausesAdded& added_cls);
        set<uint32_t> get_vars_in_poly(const BoolePolynomial& poly) const;
        vector<uint32_t> add_to_poly_vars_until_cutoff(BoolePolynomial& thisPoly, set<uint32_t>& vars);

        //Main adders
        pair<uint32_t, ClausesAdded> addBooleMonomial(const BooleMonomial& m);

        //Adding as non-xor clause
        ClausesAdded addXorClauseAsNormals(const XorClause& cl, const BoolePolynomial& poly);
        uint32_t hammingWeight(uint64_t num) const;
        void addEveryCombination(vector<uint32_t>& vars, bool isTrue, vector<Clause>& thisClauses);

        //Setup
        Karnaugh karn;
        const ConfigData& config;
        const ANF& anf;

        //The cumulated CNF data
        vector<pair<vector<Clause>, BoolePolynomial> > clauses;
        vector<pair<Lit, BoolePolynomial> > assumptions;

        //uint32_t maps -- internal/external mapping of variables/monomial/polynomials
        std::map<BooleMonomial, uint32_t> monomMap; ///<map: outside monom -> inside var
        std::map<uint32_t, BooleMonomial> revMonomMap; ///<map: inside var -> outside monom
        std::map<uint32_t, BoolePolynomial> varToXorMap; ///<When cutting XORs, which var represents which XOR cut. Poly is of degree 1 here of course
        uint32_t next_cnf_var = 0; ///<CNF variable counter

        //stats
        size_t addedAsANF = 0;
        size_t addedAsSimpleANF = 0;
        size_t addedAsComplexANF = 0;
        size_t addedAsCNF = 0;
};

inline std::ostream& operator<<(std::ostream& os, const CNF& cnf)
{
    os << "p cnf " << cnf.getNumVars() << " " << cnf.getNumAllClauses() << std::endl;

    for(vector<pair<vector<Clause>, BoolePolynomial> >::const_iterator it = cnf.clauses.begin(), end = cnf.clauses.end(); it != end; it++) {
        const vector<Clause>& clauses = it->first;
        for (vector<Clause>::const_iterator it2 = clauses.begin(), end2 = clauses.end(); it2 != end2; it2++) {
            os << *it2 << std::endl;
        }
        os << "c " << it->second << std::endl;
        os << "c ------------";
        if (it+1 != cnf.clauses.end()) {
            os << std::endl;
        }
    }

    return os;
}

inline bool CNF::varRepresentsMonomial(const uint32_t var) const
{
    map<uint32_t, BoolePolynomial>::const_iterator it = varToXorMap.find(var);
    return (it == varToXorMap.end());
}

inline size_t CNF::getNumClauses() const
{
    return clauses.size();
}

inline size_t CNF::getAddedAsCNF() const
{
    return addedAsCNF;
}

inline size_t CNF::getAddedAsANF() const
{
    return addedAsANF;
}

inline size_t CNF::getAddedAsSimpleANF() const
{
    return addedAsSimpleANF;
}

inline size_t CNF::getAddedAsComplexANF() const
{
    return addedAsComplexANF;
}

inline const vector<pair<vector<Clause>, BoolePolynomial> >& CNF::getClauses() const
{
    return clauses;
}

inline const vector<pair<Lit, BoolePolynomial> >& CNF::getAssumptions() const {
    return assumptions;
}

inline uint32_t CNF::getNumVars() const
{
    return next_cnf_var;
}

inline void CNF::print_stats() const
{
    cout << "c Clauses              : " << getNumClauses() << endl;
    cout << "c Added as CNF         : " << getAddedAsCNF() << endl;
    cout << "c Added as simple ANF  : " << getAddedAsSimpleANF() << endl;
    cout << "c Added as complex  ANF: " << getAddedAsComplexANF() << endl;
}

#endif //__CNF_H__

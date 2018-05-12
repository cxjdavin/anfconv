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

#include "cnf.h"
#include <iostream>
#include <ostream>
#include <iterator>

//#define DEBUG_KARNAUGH

CNF::CNF(const ANF& _anf, const ConfigData& _config) :
    config(_config)
    , anf(_anf)
{
    //Make sure outside var X is inside var X
    assert(monomMap.empty());
    assert(revMonomMap.empty());
}

ClausesAdded CNF::init()
{
    ClausesAdded clAdded;

    //Check which variables to add
    vector<uint32_t> varsToAdd;
    //Add ALL variables
    for(size_t i = 0; i < anf.getRing().nVariables(); i++) {
        varsToAdd.push_back(i);
    }

    //Add these variables
    assert(next_cnf_var == 0);
    for(const uint32_t var: varsToAdd) {
        monomMap[BooleVariable(var, anf.getRing())] = next_cnf_var;
        revMonomMap.insert(std::make_pair(next_cnf_var, BooleVariable(var, anf.getRing())));
        next_cnf_var++;
    }

    //If ANF is not OK, then add polynomial '1'
    if (!anf.getOK()) {
        return addBoolePolynomial(BoolePolynomial(true, anf.getRing()));
    }

    return clAdded;
}

void CNF::add_trivial_equations()
{
    for(size_t i = 0; i < anf.getRing().nVariables(); i++) {
        //Add variables already set
        if (anf.value(i) != l_Undef) {
            BoolePolynomial poly(false, anf.getRing());
            poly += BooleVariable(i, anf.getRing());
            poly += BooleConstant(anf.value(i) == l_True);
            addBoolePolynomial(poly);
        }

        //Add variables replaced
        if (anf.getReplaced(i).var() != i) {
            const Lit replacedWith = anf.getReplaced(i);
            BoolePolynomial poly(false, anf.getRing());
            poly += BooleConstant(replacedWith.sign());
            poly += BooleVariable(replacedWith.var(), anf.getRing());
            poly += BooleVariable(i, anf.getRing());
            addBoolePolynomial(poly);
        }
    }
}

void CNF::addAllEquations()
{
    //Add replaced and set variables to CNF
    add_trivial_equations();

    //Add regular equations
    const vector<BoolePolynomial>& eqs = anf.getEqs();
    for (vector<BoolePolynomial>::const_iterator it = eqs.begin(), end = eqs.end(); it != end; it++) {
        addBoolePolynomial(*it);
    }
}

bool CNF::try_adding_poly_with_karn(const BoolePolynomial& eq, ClausesAdded& cls_added)
{
    vector<Clause> cls = karn.convert(eq);

    //Estimate CNF cost
    uint32_t cnfCost = 0;
    for (vector<Clause>::const_iterator
        it = cls.begin(), end = cls.end()
        ; it != end
        ; it++
    ) {
        cnfCost += it->size();
        cnfCost += 2;
    }

    //Estimate ANF cost
    uint32_t anfCost = 0;
    for(BoolePolynomial::const_iterator
        it = eq.begin(), end = eq.end()
        ; it != end
        ; it++
    ) {
        anfCost += it->deg()*2;
        anfCost += 5;
    }

    if (anfCost >= cnfCost
        || (eq.terms().size() == (1UL + (size_t)eq.hasConstantPart()))
    ) {
        addedAsCNF++;
        vector<Clause> setOfClauses;
        for(vector<Clause>::const_iterator it = cls.begin(), end = cls.end(); it != end; it++) {
            setOfClauses.push_back(*it);
        }
        clauses.push_back(std::make_pair(setOfClauses, eq));

        cls_added = ClausesAdded(setOfClauses);
        return true;
    }

    return false;
}

XorClause CNF::xor_clause_from_poly(const BoolePolynomial& eq, ClausesAdded& added_cls)
{
    XorClause cl(std::numeric_limits<uint32_t>::max(), eq.hasConstantPart());
    for (BoolePolynomial::const_iterator it = eq.begin(), end = eq.end(); it != end; it++) {
        if (it->isConstant())
            continue;

        pair<uint32_t, ClausesAdded> ret = addBooleMonomial(*it);
        cl ^= XorClause(ret.first);
        added_cls.merge(ret.second);
    }

    return cl;
}

ClausesAdded CNF::addBoolePolynomial(const BoolePolynomial& eq2)
{
    //if UNSAT, make it UNSAT
    if (eq2.isOne()) {
        vector<Clause> tmp;
        vector<Lit> lits;
        tmp.push_back(Clause(lits));
        clauses.push_back(std::make_pair(tmp, eq2));
        return ClausesAdded(tmp);
    }

    if (eq2.isZero()) {
        return ClausesAdded();
    }

    if (config.useKarn
        && eq2.deg() > 1
        && karn.possibleToConv(eq2)
    ) {
        ClausesAdded tmp;
        bool OK = try_adding_poly_with_karn(eq2, tmp);
        if (OK) {
            return tmp;
        }
    }

    //Represent using XOR & monomial combination
    //1) add monmials
    //2) add XOR
    addedAsANF++;
    if (eq2.deg() < 2) {
        addedAsSimpleANF++;
    } else {
        addedAsComplexANF++;
    }

    ClausesAdded addedClauses;
    XorClause cl = xor_clause_from_poly(eq2, addedClauses);
    ClausesAdded thisAdded = addXorClauseAsNormals(cl, eq2);
    addedClauses.merge(thisAdded);

    return addedClauses;
}

set<uint32_t> CNF::get_vars_in_poly(const BoolePolynomial& poly) const
{
    set<uint32_t> vars;
    for(BoolePolynomial::const_iterator it = poly.begin(), end = poly.end(); it != end; it++) {
        const BooleMonomial& m = *it;

        //We will deal with the +1 given cl.getConst()
        if (m.deg() == 0)
            continue;

        //Update to CNF (external) variable numbers
        map<BooleMonomial, uint32_t>::const_iterator findIt = monomMap.find(*it);
        assert(findIt != monomMap.end()); //We have added all monoms once we are here

        vars.insert(findIt->second);
    }

    return vars;
}

vector<uint32_t> CNF::add_to_poly_vars_until_cutoff(BoolePolynomial& thisPoly, set<uint32_t>& vars)
{
    vector<uint32_t> vars_added;
    uint32_t added = 0;
    for(set<uint32_t>::const_iterator it = vars.begin(); it != vars.end(); it++, added++) {
        if (added >= config.cutNum) break;
        vars_added.push_back(*it);

        map<uint32_t, BooleMonomial>::const_iterator findIt = revMonomMap.find(*it);
        if (findIt != revMonomMap.end()) {
            thisPoly += findIt->second;
        } else {
            map<uint32_t, BoolePolynomial>::const_iterator findIt2 = varToXorMap.find(*it);
            assert(findIt2 != varToXorMap.end() && "var has to be either a monom or a cut XOR!");
            thisPoly += findIt2->second;
        }
    }

    //Remove vars from set
    for(uint32_t var: vars_added) {
        vars.erase(var);
    }

    return vars_added;
}

ClausesAdded CNF::addXorClauseAsNormals(const XorClause& cl, const BoolePolynomial& poly)
{
    assert(config.cutNum > 1);

    set<uint32_t> vars = get_vars_in_poly(poly);

    vector<Clause> thisClauses;
    while (!vars.empty()) {
        uint32_t varAdded = std::numeric_limits<uint32_t>::max();

        //If have to cut, create new var
        if (vars.size() > config.cutNum) {
            varAdded = next_cnf_var;
            //std::cout << "Adding cutting var: " << (varAdded) << std::endl;
            next_cnf_var++;
        }

        //Add variables to clause
        BoolePolynomial thisPoly(false, anf.getRing());
        vector<uint32_t> vars_in_xor = add_to_poly_vars_until_cutoff(thisPoly, vars);

        //add the representative var (if appropriate)
        if (varAdded != std::numeric_limits<uint32_t>::max()) {
            varToXorMap.insert(make_pair(varAdded, thisPoly));
            vars.insert(varAdded); //Adding representative to orig set
            vars_in_xor.push_back(varAdded); //This will be the definition of the representive
        }

        bool result = false;
        if (varAdded == std::numeric_limits<uint32_t>::max()) {
            result = cl.getConst();
        }
        addEveryCombination(vars_in_xor, result, thisClauses);
    }

    clauses.push_back(make_pair(thisClauses, poly));
    return thisClauses;
}

uint32_t CNF::hammingWeight(uint64_t num) const
{
    uint32_t ret = 0;
    for(uint32_t i = 0; i < 64; i ++) {
        ret += ((num >> i) & 1UL);
    }

    return ret;
}

void CNF::addEveryCombination(vector<uint32_t>& vars, bool isTrue, vector<Clause>& thisClauses)
{
    const uint64_t max = 1UL << vars.size();
    for (uint32_t i = 0; i < max; i++) {
        //even hamming weight -> it is true
        if (hammingWeight(i) % 2 == isTrue)
            continue;

        vector<Lit> lits;
        for (size_t i2 = 0; i2 < vars.size(); i2++) {
            const bool sign = (i >>i2)&1;
            lits.push_back(Lit(vars[i2], sign));
        }
        thisClauses.push_back(Clause(lits));
    }
}

pair<uint32_t, ClausesAdded> CNF::addBooleMonomial(const BooleMonomial& m)
{
    if (m.isConstant()) {
        std::cout << "The CNF class doesn't handle adding BooleMonomials that are empty" << std::endl;
        exit(-1);
    }

    //monomial already known, return it
    map<BooleMonomial, uint32_t>::iterator it = monomMap.find(m);
    if (it != monomMap.end())
        return make_pair(it->second, ClausesAdded());

    //create monomial, as well as the corresponding clauses
    const uint32_t newVar = next_cnf_var;
    monomMap[m] = next_cnf_var;
    revMonomMap.insert(std::make_pair(next_cnf_var, m));
    next_cnf_var++;
    //std::cout << "Added revMonomMap " << newVar << " for monomial " << m << std::endl;

    //Check that all variables exist&create m2 that is the monom in internal representation
    BooleMonomial m2(anf.getRing());
    for (BooleMonomial::const_iterator it = m.begin(), end = m.end(); it != end; it++) {
        auto it2 = monomMap.find(BooleVariable(*it, anf.getRing()));
        assert(it2 != monomMap.end());
        m2 *= BooleVariable(it2->second, anf.getRing());
    }

    vector<Clause> setOfClauses;
    //create clauses e.g. '-a b', '-a c', '-a d' , etc.
    vector<Lit> lits;
    for(BooleMonomial::const_iterator it = m2.begin(), end = m2.end(); it != end; it++) {
        lits.clear();
        lits.push_back(Lit(newVar, true));
        lits.push_back(Lit(*it, false));
        setOfClauses.push_back(Clause(lits));
    }

    //create final clause e.g. 'a -b -c -d'
    lits.clear();
    lits.push_back(Lit(newVar, false));
    for(BooleMonomial::const_iterator it = m2.begin(), end = m2.end(); it != end; it++) {
        lits.push_back(Lit(*it, true));
    }
    setOfClauses.push_back(Clause(lits));

    ClausesAdded clAdded;
    clAdded.clauses = setOfClauses;

    clauses.push_back(std::make_pair(setOfClauses, m));

    return make_pair(newVar, clAdded);
}

vector<lbool> CNF::mapSolToOrig(const std::map<uint32_t, lbool>& solution) const
{
    vector<lbool> ret;
    if (solution.size() != next_cnf_var) {
        std::cerr << "ERROR: The CNF gave a solution to " << solution.size()
        << " variables but there are only " << next_cnf_var
        << " variables according to our count!" << endl;
        assert(false);
    }

    for(map<uint32_t, lbool>::const_iterator it = solution.begin(), end = solution.end(); it != end; it++) {
        map<uint32_t, BoolePolynomial>::const_iterator findIt = varToXorMap.find(it->first);
        if (findIt != varToXorMap.end()) {
            //This var represents a partial XOR chain.
            //i.e. It doesn't represent any variable outside
            continue;
        }

        //cout << "solution var:" << it->first << " val:" << it->second << endl;

        map<uint32_t, BooleMonomial>::const_iterator it2 = revMonomMap.find(it->first);
        assert(it2 != revMonomMap.end());

        //Only single-vars
        if (it2->second.deg() == 1) {
            const uint32_t var = it2->second.firstVariable().index();
            if (ret.size() <= var) ret.resize(var+1, l_Undef);
            ret[var] = it->second;
        }
    }

    return ret;
}

BooleMonomial CNF::getMonomForVar(const uint32_t& var) const
{
    map<uint32_t, BooleMonomial>::const_iterator it = revMonomMap.find(var);
    assert(it != revMonomMap.end());

    return it->second;
}

void CNF::printMonomMap() const
{
    for(map<BooleMonomial, uint32_t>::const_iterator it = monomMap.begin(), end = monomMap.end(); it != end; it++) {
        std::cout << "Inside monom " << it->first << " is outside var in CNF: " << it->second+1 << std::endl;
    }

    for(map<uint32_t, BooleMonomial>::const_iterator it = revMonomMap.begin(), end = revMonomMap.end(); it != end; it++) {
        std::cout << "Outside var in CNF " << it->first+1 << " is inside monomial: " << it->second << std::endl;
    }
}

uint64_t CNF::getNumAllLits() const
{
    uint64_t numLits = 0;
    for(vector<pair<vector<Clause>, BoolePolynomial> >::const_iterator it = clauses.begin(), end = clauses.end(); it != end; it++) {
        const vector<Clause>& thisClauses = it->first;
        for(vector<Clause>::const_iterator itCls = thisClauses.begin(), endCls = thisClauses.end(); itCls != endCls; itCls++) {
            numLits += itCls->size();
        }
    }

    return numLits;
}

uint64_t CNF::getNumAllClauses() const
{
    uint64_t numClauses = 0;
    for(vector<pair<vector<Clause>, BoolePolynomial> >::const_iterator it = clauses.begin(), end = clauses.end(); it != end; it++) {
        numClauses += it->first.size();
    }

    return numClauses;
}

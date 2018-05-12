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

#include "simplifybysat.h"
#include "satsolve.h"
#include "cryptominisat5/cryptominisat.h"

using std::cout;
using std::endl;

SimplifyBySat::SimplifyBySat(
    ANF& _anf
    , const ANF& _orig_anf
    , ConfigData& _config
    , uint64_t max_confl
) :
    anf(_anf)
    , orig_anf(_orig_anf)
    , config(_config)
    , cnf(anf, _config)
{
    //No need to add trivial equations
    cnf.init();
    cnf.addAllEquations();

    //Create SAT solver
    solver = new CMSat::SATSolver();
    solver->set_verbosity(config.verbosity == 1 ? 0 : config.verbosity);
    solver->set_max_confl(max_confl);
}

SimplifyBySat::~SimplifyBySat()
{
    delete solver;
}

void SimplifyBySat::addClausesToSolver()
{
    for(const auto it: cnf.getClauses()) {
        for(const Clause& c: it.first) {
            vector<Lit> lits = c.getClause();
            solver->add_clause(lits);
        }
    }
}

void SimplifyBySat::extractUnitaries()
{
    vector<Lit> units = solver->get_zero_assigned_lits();
    if (config.verbosity >= 2)
        cout << "c Num CNF vars learnt: " << units.size() << endl;

    uint64_t numRealVarLearnt = 0;
    for(size_t i = 0; i < units.size(); i++) {
        Lit unit = units[i];

        //If var represents a partial XOR clause, skip it
        if (!cnf.varRepresentsMonomial(unit.var()))
            continue;

        BooleMonomial m = cnf.getMonomForVar(unit.var());
        assert(m.deg() > 0);

        //Monomial is high degree, and FALSE. That doesn't help much
        if (m.deg() > 1 && unit.sign() == true)
            continue;

        //If DEG is 1, then this will set the variable
        //If DEG is >0 and setting is TRUE, the addBoolePolynomial() will
        //automatically set all variables in the monomial to ONE
        BoolePolynomial poly(!unit.sign(), anf.getRing());
        poly += m;
        if (config.verbosity >= 2) {
            cout << "New truth: " << poly << endl;
        }
        anf.addBoolePolynomial(poly);

        numRealVarLearnt++;
    }

    if (config.verbosity >= 1)
        cout << "c Num ANF vars learnt: " << numRealVarLearnt << endl;
}

void SimplifyBySat::extractBinXors()
{
    vector<pair<Lit, Lit> > binXors = solver->get_all_binary_xors();
    if (config.verbosity >= 2)
        cout << "c Num CNF vars replaced:" << binXors.size() << endl;

    uint64_t numRealVarReplaced = 0;
    for(vector<pair<Lit, Lit> >::const_iterator it = binXors.begin(), end = binXors.end(); it != end; it++) {
        assert(it->first.var() != it->second.var());

        //If any of the two vars represent a partial XOR clause, skip it
        if (!cnf.varRepresentsMonomial(it->first.var())
            || !cnf.varRepresentsMonomial(it->second.var()))
        {
            continue;
        }

        BooleMonomial m1 = cnf.getMonomForVar(it->first.var());
        assert(m1.deg() > 0);
        BooleMonomial m2 = cnf.getMonomForVar(it->second.var());
        assert(m2.deg() > 0);

        if (m1.deg() > 1 || m2.deg() > 1)
            continue;

        BoolePolynomial poly((it->first.sign() ^ it->second.sign()), anf.getRing());
        poly += m1;
        poly += m2;
        if (config.verbosity >= 2) {
            cout << "New truth: " << poly << endl;
        }
        anf.addBoolePolynomial(poly);

        numRealVarReplaced++;
    }

    if (config.verbosity >= 1)
        cout << "c Num ANF vars replaced: " << numRealVarReplaced << endl;
}

bool SimplifyBySat::simplify(const bool extractBinaries)
{
    if (!anf.getOK()) {
        cout << "Nothing to simplify: UNSAT" << endl;
        return false;
    }

    //Add variables to SAT solver
    for(uint32_t i = 0; i < cnf.getNumVars(); i++) {
        solver->new_var();
    }

    //Add XOR & normal clauses from CNF
    addClausesToSolver();

    //Solve system of CNF until conflict limit
    lbool ret = solver->solve();

    //Extract data
    extractUnitaries();
    if (extractBinaries)
        extractBinXors();

    if (ret == l_Undef)
        return newTruthAdded;

    if (ret == l_False) {
        cout << "c UNSAT returned by solver" << endl;
        anf.addBoolePolynomial(BoolePolynomial(true, anf.getRing()));

        return false;
    }

    //We have a solution
    assert(ret == l_True);
    map<uint32_t, lbool> solutionFromSolver;
    for(uint32_t i = 0; i < solver->get_model().size(); i++) {
        solutionFromSolver[i] = solver->get_model()[i];
        assert(solver->get_model()[i] != l_Undef);
        if (config.verbosity >= 3) {
            cout << ((solver->get_model()[i] == l_True) ? "" : "-") << i << " ";
        }
    }
    cout << endl;

    vector<lbool> solution2 = cnf.mapSolToOrig(solutionFromSolver);
    const vector<lbool> solution = anf.extendSolution(solution2);

    if (config.verbosity) {
        printSolution(solution);
    }
    testSolution(orig_anf, solution);

    return newTruthAdded;
}

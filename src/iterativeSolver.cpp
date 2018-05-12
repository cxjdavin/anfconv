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

#include "iterativeSolver.h"
#include <fstream>

using std::endl;
using std::cout;

IterativeSolver::IterativeSolver(const ANF& _anf, const ConfigData& _config) :
    anf(_anf)
    , config(_config)
    , cnf(_anf, _config)
{
    solver = new CMSat::SATSolver();
    assert(solver->okay());
    solver->set_no_simplify();
}

IterativeSolver::~IterativeSolver()
{
    delete solver;
}

void IterativeSolver::solve()
{
    solver->new_vars(anf.getNumVars());

    //Add vars to CNF
    ClausesAdded clAdded = cnf.init();

    assert(solver->okay());
    const ClausesAdded added = all_clauses();
    addClauses(added);

    if (!solver->okay()) {
        cout << "UNSAT." << endl;
        return;
    }

    for(uint32_t i2 = 0; i2 < config.numIters; i2++) {
        CMSat::lbool status = solver->solve();
        if (!solver->okay() || status == CMSat::l_False) {
            cout << "UNSAT!?" << endl;
            return;
        }

        cout << "Iteration " << i2 << " solving complete"
        << endl;
    }
}

const ClausesAdded IterativeSolver::all_clauses()
{
    uint32_t numNoDefinition = 0;
    ClausesAdded added;
    for(size_t i = 0; i < anf.getEqs().size(); i++) {
        const BoolePolynomial& poly = anf.getEqs()[i];

        ClausesAdded thisAdded = cnf.addBoolePolynomial(poly);
        added.merge(thisAdded);
    }
    return added;
}

void IterativeSolver::addNewVarsIfNeedBe(const vector<Lit>& lits)
{
    for(const Lit lit: lits) {
        while(solver->nVars() <= lit.var())
            solver->new_var();
    }
}

void IterativeSolver::addNewVarsIfNeedBe(const vector<uint32_t>& vars)
{
    for(const uint32_t var: vars) {
        while(solver->nVars() <= var)
            solver->new_var();
    }
}

void IterativeSolver::addClauses(const ClausesAdded& toAdd)
{
    for(const XorClause& cl: toAdd.xorclauses) {
        vector<uint32_t> vars = cl.getClause();
        addNewVarsIfNeedBe(vars);
        solver->add_xor_clause(vars, cl.getConst());
    }

    for(const Clause& cl: toAdd.clauses) {
        vector<Lit> lits = cl.getClause();
        addNewVarsIfNeedBe(lits);
        solver->add_clause(lits);
    }
}

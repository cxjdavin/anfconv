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

#include "anf.h"
#include <string>
#include <fstream>
#include "replacer.h"
#include <boost/lexical_cast.hpp>

using std::cout;
using std::endl;
using boost::lexical_cast;

ANF::ANF(polybori::BoolePolyRing* _ring,  ConfigData& _config) :
        ring(_ring), config(_config), replacer(NULL) {
    replacer = new Replacer;

    //ensure that the variables are not new
    for (size_t i = 0; i < ring->nVariables(); i++) {
        replacer->newVar(i);
    }

    assert(occur.empty());
    occur.resize(ring->nVariables());
}

ANF::~ANF() {
    delete replacer;
}

size_t ANF::readFile(const std::string& filename, const bool addPoly) {
    // Read in the file line by line
    vector<std::string> text_file;

    size_t maxVar = 0;

    std::ifstream ifs;
    ifs.open(filename.c_str());
    if (!ifs) {
        cout << "Problem opening file: \"" << filename << "\" for reading\n";
        exit(-1);
    }
    std::string temp;

    while( std::getline( ifs, temp ) ) {
        // Empty lines are ignored
        if (temp.length() == 0) {
            continue;
        }

        // Save comments
        if (temp.length() > 0 && temp[0] == 'c') {
            comments.push_back(temp);
            continue;
        }

        BoolePolynomial eq(*ring);
        BoolePolynomial eqDesc(*ring);
        bool startOfVar = false;
        bool readInVar = false;
        bool readInDesc = false;
        size_t var = 0;
        BooleMonomial m(*ring);
        for (uint32_t i = 0; i < temp.length(); i++) {

            //Handle description separator ','
            if (temp[i] == ',') {
                if (readInVar) {
                    if (addPoly)
                        m *= BooleVariable(var, *ring);

                    eq += m;
                }

                startOfVar = false;
                readInVar = false;
                var = 0;
                m = BooleMonomial(*ring);
                readInDesc = true;
                continue;
            }

            //Silently ignore brackets.
            //This makes the 'parser' work for both "x3" and "x(3)"
            if (temp[i] == ')' || temp[i] == '(') {
                continue;
            }

            //Space means end of variable
            if (temp[i] == ' ') {
                if (startOfVar && !readInVar) {
                    cout
                    << "x is not followed by number at this line : \"" << temp << "\""
                    << endl;
                    exit(-1);
                }
                startOfVar = false;
                continue;
            }

            if (temp[i] == 'x' || temp[i] == 'X') {
                startOfVar = true;
                readInVar = false;
                continue;
            }

            //Handle constant '1'
            if (temp[i] == '1' && !startOfVar) {
                if (!readInDesc) eq += BooleConstant(true);
                else eqDesc += BooleConstant(true);
                readInVar = false;
                continue;
            }

            //Handle constant '0'
            if (temp[i] == '0' && !startOfVar) {
                if (!readInDesc) eq += BooleConstant(false);
                else eqDesc += BooleConstant(false);
                readInVar = false;
                continue;
            }

            if (temp[i] == '+') {
                if (readInVar) {
                    if (addPoly)
                        m *= BooleVariable(var, *ring);

                    if (!readInDesc) eq += m;
                    else eqDesc += m;
                }

                startOfVar = false;
                readInVar = false;
                var = 0;
                m = BooleMonomial(*ring);
                continue;
            }

            if (temp[i] == '*') {
                if (!readInVar) {
                    cout
                    << "No variable before \"*\" in equation: \"" << temp << "\""
                    << endl;
                    exit(-1);
                }

                //Multiplying current var into monomial
                if (addPoly)
                    m *= BooleVariable(var, *ring);

                startOfVar = false;
                readInVar = false;
                var = 0;
                continue;
            }

            //At this point, only numbers are valid
            if (temp[i] < '0' || temp[i] > '9') {
                cout
                << "Unknown character \"" << temp[i] << "\" in equation: \"" << temp << "\""
                << endl;
                exit(-1);
            }

            if (!startOfVar) {
                cout
                << "Value of var before \"x\" in equation: \"" << temp << "\""
                << endl;
                exit(-1);
            }
            readInVar = true;
            int vartmp = temp[i] - '0';
            assert(vartmp >= 0 && vartmp <= 9);
            var *= 10;
            var += vartmp;

            //This variable will be used, no matter what, so use it as max
            maxVar = std::max(maxVar, var);
        }

        //If variable was being built up when the line ended, add it
        if (readInVar) {
            if (addPoly)
                m *= BooleVariable(var, *ring);

            if (!readInDesc) eq += m;
            else eqDesc += m;
        }

        //Set state to starting position
        startOfVar = false;
        readInVar = false;
        var = 0;
        m = BooleMonomial(*ring);

        size_t realTermsSize = eqDesc.length() - (int)eqDesc.hasConstantPart();
        if (realTermsSize > 1) {
            cout
            << "ERROR!" << endl
            << "After the comma, only a monomial is supported (not an equation)"
            << endl
            << "But You gave: " << eqDesc << " on line: '" << temp << "'"
            << endl;
            exit(-1);
        }

        if (realTermsSize == 1 && eqDesc.firstTerm().deg() > 1) {
            cout
            << "ERROR! " << endl
            << "After the comma, only a single-var monomial is supported (no multi-var monomial)"
            << endl
            << "You gave: " << eqDesc << " on line: " << temp
            << endl;
            exit(-1);
        }

        if (addPoly) {
            addBoolePolynomial(eq);
        }
    }

    ifs.close();
    return maxVar;
}

bool ANF::addBoolePolynomial(const BoolePolynomial& poly) {
    // Don't add constants
    if (poly.isConstant()) {
        // Check UNSAT
        if (poly.isOne()) {
            replacer->setNOTOK();
        }
        return false;
    }

    // If poly already present, don't add it
    for (const BoolePolynomial& existing : eqs) {
        if (existing == poly) {
            return false;
        }
    }

    addPolyToOccur(poly, eqs.size());
    eqs.push_back(poly);
    for (const uint32_t& v : poly.usedVariables()) {
        updatedVars.insert(v);
    }
    return true;
}

bool ANF::addLearntBoolePolynomial(const BoolePolynomial& poly) {
    // Contextualize it to existing knowledge
    BoolePolynomial contextualized_poly = replacer->update(poly);
    bool added = addBoolePolynomial(contextualized_poly);
    if (added && config.verbosity >= 4) {
        cout << "c Adding: " << poly << endl
             << "c as: " << contextualized_poly << endl;
    }
    return added;
}

// Slow. O(n^2) because cannot use set<> for BoolePolynomial
vector<BoolePolynomial>* ANF::contextualizedLearnt(const vector<BoolePolynomial>& loop_learnt) {
    vector<BoolePolynomial>* all_learnt = new vector<BoolePolynomial>();
    for (const BoolePolynomial& poly : loop_learnt) {
        BoolePolynomial contextualized_poly = replacer->update(poly);
        all_learnt->push_back(contextualized_poly);
    }
    return all_learnt;
}

void ANF::addPolyToOccur(const BoolePolynomial& poly, const size_t eq_idx) {
    for (const uint32_t var_idx : poly.usedVariables()) {
        occur[var_idx].push_back(eq_idx);
    }
}

void ANF::removePolyFromOccur(const BoolePolynomial& poly, size_t eq_idx) {
    //Remove from occur
    for (const uint32_t var_idx : poly.usedVariables()) {
        vector<size_t>::iterator findIt = std::find(occur[var_idx].begin(), occur[var_idx].end(), eq_idx);
        assert(findIt != occur[var_idx].end());
        occur[var_idx].erase(findIt);
    }
}

void ANF::propagate() {
    // Always run through all variables
    for (uint32_t v = 0; v < ring->nVariables(); v++) {
        updatedVars.insert(v);
    }

    //Recursively update polynomials, while there is something to update
    while (!updatedVars.empty()) {
        // Make a copy of what variables to iterate through in this cycle
        set<uint32_t> updatedVars_snapshot = updatedVars;
        updatedVars.clear();
        for (const uint32_t& var_idx : updatedVars_snapshot) {
            assert(occur.size() > var_idx);
            if (config.verbosity >= 5) {
                cout << "c Updating variable " << var_idx << endl;
            }
            // We will remove and add stuff to occur, so iterate over a snapshot
            const vector<size_t> occur_snapshot = occur[var_idx];
            for (const size_t& eq_idx : occur_snapshot) {
                assert(eqs.size() > eq_idx);
                BoolePolynomial& poly = eqs[eq_idx];
                if (config.verbosity >= 5) {
                    cout << "c equation: " << poly << endl;
                }
                removePolyFromOccur(poly, eq_idx);
                poly = replacer->update(poly);

                if (poly.isConstant()) {
                    //Check UNSAT
                    if (poly.isOne()) {
                        replacer->setNOTOK();
                        return;
                    }
                } else {
                    //
                    // Assign values
                    //
                    // If polynomial is "x = 0" or "x + 1 = 0", set the value of x
                    if (poly.length() - (int)poly.hasConstantPart() == 1 && poly.deg() == 1) {
                        // Make the update
                        uint32_t v = poly.usedVariables().firstVariable().index();
                        vector<uint32_t> ret = replacer->setValue(v, poly.hasConstantPart());

                        // Mark updated vars
                        for (const uint32_t& updated_var : ret) {
                            updatedVars.insert(updated_var);
                        }
                    }

                    // If polynomial is "a*b*c*.. + 1 = 0", then all variables must be TRUE
                    if (poly.length() == 2 && poly.hasConstantPart()) {
                        for (const uint32_t& var_idx : poly.firstTerm()) {
                            // Make the update
                            vector<uint32_t> ret = replacer->setValue(var_idx, true);

                            // Mark updated vars
                            for (const uint32_t var_idx2 : ret) {
                                updatedVars.insert(var_idx2);
                            }
                        }
                    }

                    //
                    // Assign anti/equivalences
                    //
                    // If polynomial is "x + y = 0" or "x + y + 1 = 0", set the value of x in terms of y
                    if (poly.length() - (int)poly.hasConstantPart() == 2 && poly.deg() == 1) {
                        BooleMonomial m1 = poly.terms()[0];
                        BooleMonomial m2 = poly.terms()[1];

                        assert(m1.deg() == 1);
                        assert(m2.deg() == 1);
                        uint32_t var1 = m1.firstVariable().index();
                        uint32_t var2 = m2.firstVariable().index();

                        // Make the update
                        vector<uint32_t> ret = replacer->setReplace(var1, Lit(var2, poly.hasConstantPart()));
                        updatedVars.insert(var1);
                        updatedVars.insert(var2);

                        // Mark updated vars
                        for (const uint32_t& var_idx : ret) {
                            updatedVars.insert(var_idx);
                        }
                    }

                    // Add back to occur
                    addPolyToOccur(poly, eq_idx);
                }
            }
        }
    }

    removeEmptyEquations();
    checkSimplifiedPolysContainNoSetVars();
}

void ANF::checkSimplifiedPolysContainNoSetVars() const {
    for (const BoolePolynomial& poly : eqs) {
        for (const uint32_t var_idx : poly.usedVariables()) {
            if (value(var_idx) != l_Undef) {
                cout << "ERROR: Variable " << var_idx
                     << " is inside equation " << poly
                     << " even though its value is " << value(var_idx)
                     << " !!\n";
                exit(-1);
            }
        }
    }
}

void ANF::removeEmptyEquations() {
    vector<BoolePolynomial> new_eqs;
    vector<size_t> occur_delta(eqs.size(), 0);

    for (size_t i = 0; i < eqs.size(); i++) {
        const BoolePolynomial& eq = eqs[i];
        if (eq.isConstant() && eq.isZero()) {
            //If equation is constant zero, don't add to new_eqs
            //and update the occur_delta for all future equations
            for (size_t i2 = i; i2 < eqs.size(); i2++) {
                occur_delta[i2]++;
            }
        } else {
            //Not constant zero, so add
            new_eqs.push_back(eq);
        }
    }

    //Go through each variable occurance
    for (vector<size_t>& var_occur : occur) {
        //The indexes of the equations have changed. Update them.
        for (size_t& eq_idx : var_occur) {
            assert(eq_idx >= occur_delta[eq_idx]);
            eq_idx -= occur_delta[eq_idx];
        }
    }
    eqs = new_eqs;
}

bool ANF::evaluate(const vector<lbool>& vals) const {
    bool ret = true;
    for (const BoolePolynomial& poly : eqs) {
        lbool lret = evaluatePoly(poly, vals);
        assert(lret != l_Undef);

        //OOps, grave bug in implmenetation
        if (lret != l_True) {
            cout
            << "Internal ERROR! Solution doesn't satisfy eq '"
            << poly << "'"
            << endl;
            exit(-1);
        }

        ret &= (lret == l_True);
    }

    bool toadd = replacer->evaluate(vals);
    if (!toadd) {
        cout << "Replacer not satisfied" << endl;
        exit(-1);
    }
    ret &= toadd;
    return ret;
}

void ANF::checkOccur() const {
    for (const vector<size_t>& var_occur : occur) {
        for (const size_t eq_idx : var_occur) {
            assert(eq_idx < eqs.size());
        }
    }
    if (config.verbosity >= 3) {
        cout << "Sanity check passed" << endl;
    }
}

int ANF::extendedLinearization(vector<BoolePolynomial>& loop_learnt) {
    int num_learnt = 0;
    if (eqs.size() == 0) {
        if (config.verbosity >= 3) {
            cout << "c System is empty. Skip XL\n";
        }
    } else if (config.nolimiters || log2(eqs.size()) + log2(numUniqueMonoms(eqs)) <= 30) {
        vector<BoolePolynomial> equations;
        map<uint32_t, vector<BoolePolynomial> > deg_buckets;
        unordered_set<uint32_t> unique_poly_degrees;
        vector<uint32_t> sorted_poly_degrees;
  
        // Clone original system while putting them into degree buckets
        for (const BoolePolynomial& poly : eqs) {
            equations.push_back(poly);
            uint32_t poly_deg = poly.deg();
            unique_poly_degrees.insert(poly_deg);
            if (deg_buckets.find(poly_deg) == deg_buckets.end()) {
                deg_buckets[poly_deg] = vector<BoolePolynomial>();
            }
            deg_buckets[poly_deg].push_back(poly);
        }
        sorted_poly_degrees.assign(unique_poly_degrees.begin(), unique_poly_degrees.end());
        sort(sorted_poly_degrees.begin(), sorted_poly_degrees.end());

        // Expansion step
        bool done_expansion = false;
        unsigned long nVars = ring->nVariables();
        for (uint32_t deg = 1; deg <= config.xlDeg && !done_expansion; deg++) {
            for (uint32_t poly_deg : sorted_poly_degrees) {
                const vector<BoolePolynomial>& to_expand = deg_buckets[poly_deg];
                if (config.verbosity >= 3) {
                    cout << "c There are " << to_expand.size() << " polynomials of degree " << poly_deg << endl;
                }
                for (const BoolePolynomial& poly : to_expand) {
                    if (!config.nolimiters && log2(equations.size()) + log2(numUniqueMonoms(equations)) > 30) {
                        done_expansion = true;
                        break;
                    } else {
                        // Ugly hack
                        // To do: Efficient implementation of "nVars choose xlDeg"
                        //        e.g. http://howardhinnant.github.io/combinations.html?
                        if (deg >= 1) {
                            for (unsigned long i = 0; i < nVars; ++i) {
                                BooleVariable v = ring->variable(i);
                                equations.push_back(BoolePolynomial(v * poly));
                            }
                        }
                        if (deg >= 2) {
                            for (unsigned long i = 0; i < nVars; ++i) {
                                for (unsigned long j = i+1; j < nVars; ++j) {
                                    BooleVariable v1 = ring->variable(i);
                                    BooleVariable v2 = ring->variable(j);
                                    equations.push_back(BoolePolynomial(v1 * v2 * poly));
                                }
                            }
                        }
                        if (deg >= 3) {
                            for (unsigned long i = 0; i < nVars; ++i) {
                                for (unsigned long j = i+1; j < nVars; ++j) {
                                    for (unsigned long k = j+1; k < nVars; ++k) {
                                        BooleVariable v1 = ring->variable(i);
                                        BooleVariable v2 = ring->variable(j);
                                        BooleVariable v3 = ring->variable(k);
                                        equations.push_back(BoolePolynomial(v1 * v2 * v3 * poly));
                                    }
                                }
                            }
                        }
                    }
                }
                if (done_expansion) {
                    break;
                }
            }
        }
        // Run GJE after expansion
        if (config.verbosity >= 2) {
            cout << "c XL system is " << equations.size() << " x " << numUniqueMonoms(equations) << endl;
        }
        GaussJordan gj(equations, *ring, config.verbosity);
        vector<BoolePolynomial> learnt_from_gj;
        gj.run(NULL, &learnt_from_gj);
        for(BoolePolynomial poly : learnt_from_gj) {
            loop_learnt.push_back(poly);
            num_learnt += addLearntBoolePolynomial(poly);
        }
    }
    return num_learnt;
}

// Implementation based on https://infoscience.epfl.ch/record/176270/files/ElimLin_full_version.pdf
int ANF::elimLin(vector<BoolePolynomial>& loop_learnt) {
    vector<size_t> linear_indices;
    vector<BoolePolynomial> all_equations;
    vector<BoolePolynomial> learnt_equations;
    int num_learnt = 0;

    // Clone original system
    for (const BoolePolynomial& poly : eqs) {
        all_equations.push_back(poly);
    }

    bool fixedpoint = false;
    while (!fixedpoint) {
        fixedpoint = true;
        if (!config.nolimiters && log2(eqs.size()) + log2(numUniqueMonoms(eqs)) > 30) {
            if (config.verbosity >= 3) {
                cout << "c Matrix has over 10 million cells. Break out of EL loop\n";
            }
            break;
        }

        // Perform Gauss Jordan
        GaussJordan gj(all_equations, *ring, config.verbosity);
        int num_linear = gj.run(&all_equations, NULL);
        linear_indices.clear();
        for (size_t i = 0; i < all_equations.size(); i++) {
            if (all_equations[i].deg() == 1) {
                linear_indices.push_back(i);
            }
        }
        assert(num_linear == linear_indices.size());

        if (config.verbosity >= 3) {
            cout << "c Processing " << num_linear << " linear equations "
                 << "in a system with " << all_equations.size() << " equations\n";
        }
        if (num_linear == 0) {
            break;
        }

        // Create occurrence list for equations involved
        vector< set<size_t> > el_occ;
        for (size_t i = 0; i < ring->nVariables(); i++) {
            el_occ.push_back(set<size_t>());
        }
        for (size_t idx = 0; idx < all_equations.size(); idx++) {
            const BoolePolynomial& poly = all_equations[idx];
            for (const uint32_t v : poly.usedVariables()) {
                el_occ[v].insert(idx);
            }
        }

        // Iterate through all linear equations
        for (size_t linear_idx : linear_indices) {
            const BoolePolynomial& linear_eq = all_equations[linear_idx];
            if (!linear_eq.isConstant()) {
                fixedpoint = false;
                learnt_equations.push_back(linear_eq);

                // Pick variable which best metric to substitute
                BooleMonomial from_mono(*ring);
                BoolePolynomial to_poly(0, *ring);
                size_t best_metric = std::numeric_limits<std::size_t>::max();
                assert(linear_eq.deg() == 1);
                for (const BooleMonomial& mono : linear_eq) {
                    if (mono != BooleConstant(1)) {
                        size_t metric = occur[mono.firstVariable().index()].size();
                        if (metric < best_metric) {
                            best_metric = metric;
                            from_mono = mono;
                            to_poly = linear_eq - mono;
                        }
                    }
                }
                assert(from_mono.deg() == 1);
                uint32_t var_to_replace = from_mono.firstVariable().index();
                if (config.verbosity >= 5) {
                    cout << "c Replacing " << linear_eq.firstTerm().firstVariable()
                         << " with " << to_poly << endl;
                }

                // Eliminate variable from these polynomials
                set<size_t> to_replace = el_occ[var_to_replace];
                for (size_t idx : to_replace) {
                    BoolePolynomial& poly = all_equations[idx];

                    // Remove from el_occ
                    for (const uint32_t v : poly.usedVariables()) {
                        set<size_t>::iterator findIt = std::find(el_occ[v].begin(), el_occ[v].end(), idx);
                        assert(findIt != el_occ[v].end());
                        el_occ[v].erase(findIt);
                    }

                    // Eliminate variable
                    poly = (poly / from_mono * to_poly) + (poly % from_mono);

                    // Add back to el_occ
                    for (const uint32_t v : poly.usedVariables()) {
                        el_occ[v].insert(idx);
                    }
                }
            }
        }
    }

    // Contextualize final system
    for (BoolePolynomial& poly : all_equations) {
        poly = replacer->update(poly);

        // Add possible useful knowledge back to actual ANF system
        // 1) Linear equations (includes assignments and anti/equivalences)
        // 2) abc...z + 1 = 0
        // 3) mono1 + mono2 = 0/1
        size_t realTermsSize = poly.length() - (int) poly.hasConstantPart();
        if (poly.deg() == 1 || (realTermsSize == 1 && poly.hasConstantPart())) {
            learnt_equations.push_back(poly);
        }
    }

    // Add learnt_equations
    int linear_count = 0;
    for (const BoolePolynomial& poly : learnt_equations) {
        loop_learnt.push_back(poly);
        bool added = addLearntBoolePolynomial(poly);
        if (added) {
            num_learnt++;
            if (poly.deg() == 1) {
                linear_count++;
            }
        }
    }
    return num_learnt;
}

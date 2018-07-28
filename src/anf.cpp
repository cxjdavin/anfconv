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
    if (added && config.verbosity >= 3) {
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
        if (std::find(all_learnt->begin(), all_learnt->end(), contextualized_poly) == all_learnt->end() &&
            std::find(eqs.begin(), eqs.end(), contextualized_poly) == eqs.end()) {
            all_learnt->push_back(contextualized_poly);
        }
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

size_t ANF::evaluateMonoReplacement(const BooleMonomial& from_mono,
                                    const BoolePolynomial& to_poly,
                                    bool include_equation) {
    // Clone system
    vector<BoolePolynomial> cloned_system;
    for (const BoolePolynomial& poly : eqs) {
        cloned_system.push_back(poly);
    }

    // Try replace from_mono with to_poly
    if (include_equation) {
        cloned_system.push_back(from_mono + to_poly);
    }
    for (BoolePolynomial& poly : cloned_system) {
        BoolePolynomial newpoly(*ring);
        for (const BooleMonomial& mono : poly) {
            if (containsMono(mono, from_mono)) {
                newpoly +=  (mono / from_mono) * to_poly;
            } else {
                newpoly += mono;
            }
        }
        poly = newpoly;
    }

    // Evaluate metric
    size_t metric = numUniqueMonoms(cloned_system);
    return metric;
}

// Returns n choose r
// Note: Assume no overflow
uint32_t nCr(const uint32_t n, const uint32_t r) {
    assert(r <= n);
    uint32_t b = std::min(r, n-r);
    uint32_t ans = 1;
    for (uint32_t i = n; i > n-b; --i) {
        ans *= i;
    }
    for (uint32_t i = 1; i <= b; ++i) {
        ans /= i;
    }
    return ans;
}

int ANF::extendedLinearization(vector<BoolePolynomial>& loop_learnt) {
    int num_learnt = 0;
    int multiplier = 0;
    for (uint32_t d = 0; d <= config.xlDeg; ++d) {
        // Add (n choose d)
        multiplier += nCr(ring->nVariables(), d);
    }
    if (eqs.size() == 0) {
        if (config.verbosity >= 3) {
            cout << "c System is empty. Skip XL\n";
        }
    } else if (!config.nolimiters &&
               (double) eqs.size() * ring->nVariables() > 10000000 / multiplier) {
        if (config.verbosity >= 3) {
           cout << "c Matrix has over 10 million cells. Skip XL\n"
                << "c (This is a lower bound estimate assuming no change in numUniqueMonoms)\n";
        }
    } else {
        vector<BoolePolynomial> equations;
        for (const BoolePolynomial& poly : eqs) {
            equations.push_back(poly);
        }
        // Ugly hack
        // To do: Efficient implementation of "nVars choose xlDeg"
        //        e.g. http://howardhinnant.github.io/combinations.html?
        unsigned long nVars = ring->nVariables();
        if (config.xlDeg >= 1) {
            for (unsigned long i = 0; i < nVars; ++i) {
                BooleVariable v = ring->variable(i);
                for (const BoolePolynomial& poly : eqs) {
                    equations.push_back(BoolePolynomial(v * poly));
                }
            }
        }
        if (config.xlDeg >= 2) {
            for (unsigned long i = 0; i < nVars; ++i) {
                for (unsigned long j = i+1; j < nVars; ++j) {
                    BooleVariable v1 = ring->variable(i);
                    BooleVariable v2 = ring->variable(j);
                    for (const BoolePolynomial& poly : eqs) {
                        equations.push_back(BoolePolynomial(v1 * v2 * poly));
                    }
                }
            }
        }
        if (config.xlDeg >= 3) {
            for (unsigned long i = 0; i < nVars; ++i) {
                for (unsigned long j = i+1; j < nVars; ++j) {
                    for (unsigned long k = j+1; k < nVars; ++k) {
                        BooleVariable v1 = ring->variable(i);
                        BooleVariable v2 = ring->variable(j);
                        BooleVariable v3 = ring->variable(k);
                        for (const BoolePolynomial& poly : eqs) {
                            equations.push_back(BoolePolynomial(v1 * v2 * v3 * poly));
                        }
                    }
                }
            }
        }
        if (!config.nolimiters &&
            (double) equations.size() > 10000000 / numUniqueMonoms(equations)) {
            if (config.verbosity >= 3) {
                cout << "c Matrix has over 10 million cells. Skip XL\n";
            }
        } else {
            GaussJordan gj(equations, *ring, config.verbosity);
            vector<BoolePolynomial> truths_from_gj;
            gj.run(truths_from_gj);
            for(BoolePolynomial poly : truths_from_gj) {
                loop_learnt.push_back(poly);
                num_learnt += addLearntBoolePolynomial(poly);
            }
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
        if (!config.nolimiters &&
            all_equations.size() * numUniqueMonoms(all_equations) > 10000000) {
            if (config.verbosity >= 3) {
                cout << "c Matrix has over 10 million cells. Break out of EL loop\n";
            }
            break;
        }

        // Perform Gauss Jordan
        GaussJordan gj(all_equations, *ring, config.verbosity);
        gj.run(linear_indices, all_equations);

        if (config.verbosity >= 3) {
            cout << "c Processing " << linear_indices.size() << " linear equations "
                 << "in a system with " << all_equations.size() << " equations\n";
        }

        // Iterate through all linear equations
        for (size_t linear_idx : linear_indices) {
            const BoolePolynomial& linear_eq = all_equations[linear_idx];
            if (!linear_eq.isConstant()) {
                fixedpoint = false;
                learnt_equations.push_back(linear_eq);

                // Pick variable which best metric to substitute
                BooleMonomial from_mono(*ring);
                BoolePolynomial poly_to_replace(0, *ring);
                size_t best_metric = std::numeric_limits<std::size_t>::max();
                assert(linear_eq.deg() == 1);
                for (const BooleMonomial& mono : linear_eq) {
                    if (mono != BooleConstant(1)) {
                        const BoolePolynomial poly = linear_eq - mono;
                        uint32_t v = mono.firstVariable().index();
                        size_t metric = occur[v].size();
                        if (metric < best_metric) {
                            best_metric = metric;
                            from_mono = mono;
                            poly_to_replace = poly;
                        }
                    }
                }
                assert(from_mono.deg() == 1);
                uint32_t var_to_replace = from_mono.firstVariable().index();
                if (config.verbosity >= 5) {
                    cout << "c Replacing " << linear_eq.firstTerm().firstVariable()
                         << " with " << poly_to_replace << endl;
                }

                // Run through all equations and replace
                for (BoolePolynomial& poly : all_equations) {
                    bool has_var = false;
                    for (const uint32_t& v : poly.usedVariables()) {
                        if (v == var_to_replace) {
                            has_var = true;
                            break;
                        }
                    }

                    // Eliminate variable from this polynomial!
                    if (has_var) {
                        BoolePolynomial newpoly(0, *ring);
                        for (const BooleMonomial& mono : poly) {
                            BoolePolynomial newmono(1, *ring);
                            for (const uint32_t& v : mono) {
                                if (v == var_to_replace) {
                                    newmono *= poly_to_replace;
                                } else {
                                    newmono *= BooleVariable(v, *ring);
                                }
                            }
                            newpoly += newmono;
                        }
                        if (config.verbosity >= 5) {
                            cout << "c EL: " << poly << " => " << newpoly << endl;
                        }

                        // Overwrite
                        poly = newpoly;
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

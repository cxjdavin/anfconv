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

#include "anf.h"
#include <string>
#include <fstream>
#include "replacer.h"
#include <boost/lexical_cast.hpp>

using std::cout;
using std::endl;
using boost::lexical_cast;

//#define DEBUG_EQ_READ

ANF::ANF(polybori::BoolePolyRing* _ring,  ConfigData& _config) :
    ring(_ring)
    , config(_config)
    , replacer(NULL)
{
    replacer = new Replacer;

    //ensure that the variables are not new
    for (size_t i = 0; i < ring->nVariables(); i++) {
        replacer->newVar(i);
    }

    assert(occur.empty());
    occur.resize(ring->nVariables());
}

ANF::~ANF()
{
    delete replacer;
}

bool ANF::isSolved() const
{
    //Evaluate each and every polynomial and check if it's all satisfied
    for (const BoolePolynomial& poly : eqs) {
        lbool ret = evaluatePoly(poly, replacer->getValues());
        if (ret == l_False || ret == l_Undef) {
            return false;
        }
    }

    return true;
}

/**
 * @short Parses up a file with polynomials
**/
size_t ANF::readFile(
    const std::string& filename
    , const bool addPoly
) {
    //read in the file line by line
    vector<std::string> text_file;

    size_t maxVar = 0;

    std::ifstream ifs;
    ifs.open(filename.c_str());
    if (!ifs) {
        cout << "Problem opening file: \""
        << filename
        << "\" for reading"
        << endl;

        exit(-1);
    }
    std::string temp;

    while( std::getline( ifs, temp ) ) {
        //Empty lines are ignored
        if (temp.length() == 0)
            continue;

        //Comments are saved then skipped over
        if ((temp.length() > 0 && temp[0] == 'c')) {
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
                #ifdef DEBUG_EQ_READ
                cout << "(in ',')  Built up monomial: " << m << endl;
                #endif
                m = BooleMonomial(*ring);

                #ifdef DEBUG_EQ_READ
                cout << "Reading in description. BoolePolynomial was: " << eq << endl;
                #endif
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

                #ifdef DEBUG_EQ_READ
                cout << "(in '+') Built up monomial: " << m << endl;
                #endif

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
        #ifdef DEBUG_EQ_READ
        cout << "(in final)  Built up monomial: " << m << endl;
        #endif

        //Set state to starting position
        startOfVar = false;
        readInVar = false;
        var = 0;
        m = BooleMonomial(*ring);

        #ifdef DEBUG_EQ_READ
        cout << "Adding equation: " << eq << " , " << eqDesc << endl;
        #endif

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

        if (addPoly)
            addBoolePolynomial(eq);
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

    add_poly_to_occur(poly, eqs.size());
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
    if (added && config.verbosity >= 2) {
        cout << "c Adding: " << poly
             << "c as: " << contextualized_poly << endl;
    }
    return added;
}

void ANF::add_poly_to_occur(const BoolePolynomial& poly, const size_t eq_idx)
{
    for (const uint32_t var_idx : poly.usedVariables()) {
        occur[var_idx].push_back(eq_idx);
    }
}

void ANF::remove_poly_from_occur(const BoolePolynomial& poly, size_t eq_idx)
{
    //Remove from occur
    for (const uint32_t var_idx : poly.usedVariables()) {
        vector<size_t>::iterator findIt = std::find(occur[var_idx].begin(), occur[var_idx].end(), eq_idx);
        assert(findIt != occur[var_idx].end());
        occur[var_idx].erase(findIt);
    }
}

//Simplify a single polynomial
void ANF::simplifyPolynomial(BoolePolynomial& poly, const size_t eq_idx) {
    //If poly is trivial, skip
    if (poly.isConstant()) {
        //Check UNSAT
        if (poly.isOne()) {
            replacer->setNOTOK();
        }
    } else {
        // To do
    }
}

void ANF::propagate() {
    //Recursively update polynomials, while there is something to update
    while (!updatedVars.empty()) {
        // Make a copy of what variables to iterate through in this cycle
        set<uint32_t> updatedVars_snapshot = updatedVars;
        updatedVars.clear();
        for (const uint32_t& var_idx : updatedVars_snapshot) {
            assert(occur.size() > var_idx);
            if (config.verbosity >= 2) {
                cout << "c Updating variable " << var_idx << endl;
            }
            // We will remove and add stuff to occur, so iterate over a snapshot
            const vector<size_t> occur_snapshot = occur[var_idx];
            for (const size_t& eq_idx : occur_snapshot) {
                assert(eqs.size() > eq_idx);
                BoolePolynomial& poly = eqs[eq_idx];
                if (config.verbosity >= 2) {
                    cout << "c equation: " << poly << endl;
                }
                remove_poly_from_occur(poly, eq_idx);
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
                    add_poly_to_occur(poly, eq_idx);
                }
            }
        }
    }

    removeEmptyEquations();
    check_simplified_polys_contain_no_set_vars();
}

void ANF::simplify()
{
    for (size_t i = 0; i < ring->nVariables(); i++) {
        updatedVars.insert(i);
    }

    while (!updatedVars.empty()) {
        for (size_t eq_idx = 0 ; eq_idx < eqs.size(); eq_idx++) {
            simplifyPolynomial(eqs[eq_idx], eq_idx);
        }
        propagate();
    }
}

void ANF::check_simplified_polys_contain_no_set_vars() const
{
    for (const BoolePolynomial& poly : eqs) {
        for (const uint32_t var_idx : poly.usedVariables()) {
            if (value(var_idx) != l_Undef) {
                cout
                << "ERROR: Variable "
                << var_idx
                << " is inside equation "
                << poly
                << " even though its value is "
                << value(var_idx)
                << " !!" << endl;
                exit(-1);
            }
        }
    }
}

void ANF::removeEmptyEquations()
{
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

bool ANF::evaluate(const vector<lbool>& vals) const
{
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

    if (!toadd) cout << "Replacer not satisfied" << endl;
    ret &= toadd;

    return ret;
}

void ANF::printStats(int verbosity) const
{
    if (verbosity >= 1) {
        cout << "c ---- ANF stats -----" << endl;
        cout << "c Num total vars: " << getNumVars() << endl;
        cout << "c Num free vars: " << replacer->getNumUnknownVars() << endl;
        cout << "c Num equations: " << size() << endl;
        cout << "c Num monoms in eqs: " << numMonoms() << endl;
        cout << "c Max deg in eqs: " << deg() << endl;
        cout << "c Simple XORs: " << getNumSimpleXors() << endl;
        cout << "c Num vars set: " << getNumSetVars() << endl;
        cout << "c Num vars replaced: " << getNumReplacedVars() << endl;
        cout << "c --------------------" << endl;
    }
}

/**
 * @short Checks if occurrance list is (partially) OK
**/
void ANF::checkOccur() const
{
    for (const vector<size_t>& var_occur : occur) {
        for (const size_t eqn_idx : var_occur) {
            assert(eqn_idx < eqs.size());
        }
    }

    if (config.verbosity >= 2) {
        cout << "Sanity check passed" << endl;
    }
}

void ANF::preferLowVars()
{
    set<uint32_t> updatedVars2 = replacer->preferLowVars();
    updatedVars.insert(updatedVars2.begin(), updatedVars2.end());
    simplify();
}

void ANF::extractVariables(
    const size_t from
    , const size_t to
    , const vector<lbool>* sol
) const {
    uint64_t ret = 0;
    bool unknown_inside = false;
    for (size_t i = from, at = 0; i <= to; i++, at++) {
        bool setAlready = false;

        lbool val = getFixedValues()[i];
        if (val == l_False
            || (sol && sol->size() > i && (*sol)[i] == l_False)
        ) {
            cout << "0";
            setAlready = true;
            continue;
        }

        if (val == l_True
            || (sol && sol->size() > i && (*sol)[i] == l_True)
        ) {
            if (setAlready) {
                cout << "OOOOOOPS" << endl;
                exit(-1);
            }
            ret |= ((uint64_t)1) << ((to-from-1)-at);
            cout << "1";
            setAlready = true;
            continue;
        }

        if (val == l_Undef) {
            cout << "?";
            unknown_inside = true;
            continue;
        }

        assert(false);
    }
    cout << endl;

    if (unknown_inside) {
        cout
        << "Cannot give HEX representation, because unknown value was inside"
        << endl;
    } else if (to-from+1 > 64) {
        cout
        << "Cannot give HEX representation, because there were more than 64 bits"
        << endl;
    } else {
        cout << "In HEX: "
        << std::hex << std::setfill('0')
        << std::setw((to-from+1)/4 + (bool)((to-from+1) % 4))
        << ret
        << std::dec
        << endl;
    }
}


ANF* ANF::minimise(
    vector<uint32_t>& oldToNewMap
    , vector<uint32_t>& newToOldMap
) {
    vector<uint32_t> unknown = replacer->getUnknownVars();
    newToOldMap.resize(unknown.size(), std::numeric_limits<uint32_t>::max());
    oldToNewMap.resize(getNumVars(), std::numeric_limits<uint32_t>::max());

    for (size_t i = 0; i < unknown.size(); i++) {
        uint32_t oldVar = unknown[i];
        vector<uint32_t> replaces = replacer->getReplacesVars(oldVar);

        //Replaces itself and others
        oldToNewMap[oldVar] = i;
        for (uint32_t var: replaces) {
            oldToNewMap[var] = i;
        }

        newToOldMap[i] = oldVar;
    }

    BoolePolyRing* newring = new BoolePolyRing(unknown.size());
    ANF* newanf = new ANF(newring, config);

    // Update each polynomial in system
    for (const BoolePolynomial& poly : eqs) {
        BoolePolynomial newpoly(*newring);

        // Update each monomial in polynomial
        for (const BooleMonomial& mono : poly) {
            BooleMonomial newm(*newring);

            // Update each variable in monomial
            for (const uint32_t var_idx : mono) {
                assert(oldToNewMap.size() > var_idx);
                assert(oldToNewMap[var_idx] != std::numeric_limits<uint32_t>::max());
                uint32_t newVar = oldToNewMap[var_idx];
                newm *= BooleVariable(newVar, *newring);
            }
            newpoly += newm;
        }

        newanf->addBoolePolynomial(newpoly);
    }

    return newanf;
}

int ANF::eliminate_linear(vector<BoolePolynomial>& equations) {
    vector<BoolePolynomial> useful;
    while (getNumSimpleXors(equations) != 0) {
        // Group all linear equations
        set<size_t> linear_indices;
        for (size_t eqn_idx = 0; eqn_idx < eqs.size(); eqn_idx++) {
            if (equations[eqn_idx].deg() == 1) {
                linear_indices.insert(eqn_idx);
            }
        }

        // Iterate through all linear equations
        for (size_t linear_idx : linear_indices) {
            // Arbitrarily pick the first variable to substitute
            BoolePolynomial& linear_eq = equations[linear_idx];
            uint32_t var_to_replace = linear_eq.firstTerm().firstVariable().index();
            BoolePolynomial poly_to_replace = linear_eq + linear_eq.firstTerm().firstVariable();
            if (config.verbosity >= 2) {
                cout << "c Replacing " << linear_eq.firstTerm().firstVariable()
                     << " with " << poly_to_replace << endl;
            }

            // Run through equation set and replace
            for (size_t eqn_idx = 0; eqn_idx < eqs.size(); eqn_idx++) {
                BoolePolynomial& eq = equations[eqn_idx];
                bool has_var = false;
                for (const uint32_t& v : eq.usedVariables()) {
                    if (v == var_to_replace) {
                        has_var = true;
                        break;
                    }
                }

                // Eliminate variable from this polynomial!
                if (has_var) {
                    BoolePolynomial new_eq(0, eq.ring());
                    for (const BooleMonomial& mono : eq) {
                        BoolePolynomial new_mono(1, eq.ring());
                        for (const uint32_t& v : mono) {
                            if (v == var_to_replace) {
                                new_mono *= poly_to_replace;
                            } else {
                                new_mono *= BooleVariable(v, eq.ring());
                            }
                        }
                        new_eq += new_mono;
                    }
                    if (config.verbosity >= 2) {
                        cout << "c EL: " << eq << " => " << new_eq << endl;
                    }

                    // Add possible useful knowledge back to actual ANF system
                    // 1) Linear equations (includes assignments and anti/equivalences)
                    // 2) abc...z + 1 = 0
                    // 3) mono1 + mono2 = 0/1
                    size_t realTermsSize = new_eq.length() - (int) new_eq.hasConstantPart();
                    if (new_eq.deg() == 1
                    || (realTermsSize == 1 && new_eq.hasConstantPart())
                    || realTermsSize == 2) {
                        useful.push_back(new_eq);
                    }

                    // Overwrite
                    eq = new_eq;
                }
            }
        }
    }

    int num_learnt = 0;
    for (BoolePolynomial& poly : useful) {
        num_learnt += addLearntBoolePolynomial(poly);
    }
    return num_learnt;
}

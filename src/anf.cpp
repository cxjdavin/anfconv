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
    for(vector<BoolePolynomial>::const_iterator
        it = eqs.begin(), end = eqs.end()
        ; it != end
        ; it++
    ) {
        lbool ret = evaluatePoly(*it, replacer->getValues());
        if (ret == l_False || ret == l_Undef)
            return false;
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

            if (temp[i] == 'x') {
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

void ANF::addBoolePolynomial(const BoolePolynomial& poly)
{
    //If poly is constant, don't add it
    if (poly.isConstant()) {
        if (poly.isOne())
            replacer->setNOTOK();

        return;
    }

    //This will set 'updatedVars' and as such will allow the simplification
    //routine to execute in simplify()
    bool handled = checkIfPolyUpdatesSomething(poly, false);

    //Not handled above by replacer, add as equation
    if (!handled) {
        add_poly_to_occur(poly, eqs.size());
        eqs.push_back(poly);
    }
}

void ANF::add_poly_to_occur(const BoolePolynomial& poly, const size_t index)
{
    BooleMonomial m = poly.usedVariables();
    for(BooleMonomial::const_iterator
        it = m.begin(), end = m.end()
        ; it != end
        ; it++
    ) {
        occur[*it].push_back(index);
    }
}

void ANF::remove_poly_from_occur(const BoolePolynomial& poly, size_t index)
{
    //Remove from occur
    BooleMonomial vars(poly.usedVariables());
    for(BooleMonomial::const_iterator
        it = vars.begin(), end = vars.end()
        ; it != end
        ; it++
    ) {
        vector<size_t>::iterator findIt = std::find(occur[*it].begin(), occur[*it].end(), index);
        assert(findIt != occur[*it].end());
        occur[*it].erase(findIt);
    }
}

//Simplify a single polynomial
//-> remove from occurance list, update, then add to occurance list
void ANF::simplifyPolyonomial(
    BoolePolynomial& poly
    , const size_t index
    , const bool replace
) {
    //If poly is trivial, skip
    if (poly.isConstant()) {

        //Check UNSAT
        if (poly.isOne())
            replacer->setNOTOK();

        return;
    }

    remove_poly_from_occur(poly, index);

    //update equation & representative
    poly = replacer->update(poly);

    bool handled = checkIfPolyUpdatesSomething(poly, replace);

    if (!handled) {
        add_poly_to_occur(poly, index);
    } else {
        poly = BoolePolynomial(*ring);
    }
}

bool ANF::checkIfPolyUpdatesSomething(
    const BoolePolynomial& poly
    , const bool replace
) {

    //check for emptyness
    if (poly.isConstant()) {

        //Empty AND UNSAT?
        if (poly.hasConstantPart() == true) {
            replacer->setNOTOK();
        }

        //Don't add, it's an empty poly
        return true;
    }

    const size_t realTermsSize = poly.length() - (int)poly.hasConstantPart();

    //check for var-setting
    if (realTermsSize == 1 && poly.deg() == 1) {
        const BooleMonomial m = poly.firstTerm();

        assert(m.deg() == 1);
        uint32_t var = m.firstVariable().index();

        //make the update
        vector<uint32_t> ret = replacer->setValue(var, poly.hasConstantPart());

        //Mark updated vars
        for(vector<uint32_t>::const_iterator
            it = ret.begin(), end = ret.end()
            ; it != end
            ; it++
        ) {
            updatedVars.insert(*it);
        }

        return true;
    }

    //check for equivalence
    if (replace
        && realTermsSize == 2
        && poly.deg() == 1
    ) {
        BooleMonomial m1 = poly.firstTerm();
        BooleMonomial m2 = poly.terms()[1];

        assert(m1.deg() == 1);
        assert(m2.deg() == 1);
        uint32_t var1 = m1.firstVariable().index();
        uint32_t var2 = m2.firstVariable().index();

        //Make the update
        vector<uint32_t> ret = replacer->setReplace(var1, Lit(var2, poly.hasConstantPart()));
        updatedVars.insert(var1);
        updatedVars.insert(var2);
        for(vector<uint32_t>::const_iterator
            it = ret.begin(), end = ret.end()
            ; it != end
            ; it++
        ) {
            updatedVars.insert(*it);
        }

        return true;
    }

    //Check for a*b*c*.. = 1  --> all vars must be TRUE
    if (realTermsSize == 1 && poly.hasConstantPart()) {
        for(BooleMonomial::const_iterator
            it = poly.firstTerm().begin(), end = poly.firstTerm().end()
            ; it != end
            ; it++
        ) {
            //Make the update
            vector<uint32_t> ret = replacer->setValue(*it, true);

            //Mark updated vars
            for(vector<uint32_t>::const_iterator
                it = ret.begin(), end = ret.end()
                ; it != end
                ; it++
            ) {
                updatedVars.insert(*it);
            }
        }

        return true;
    }

    return false;
}

void ANF::simplify(const bool replace, bool all)
{
    if (all) {
        for(size_t i = 0, end = ring->nVariables()
            ; i < end
            ; i++
        ) {
            updatedVars.insert(i);
        }
    }
    //Recursively update polynomials, while there is something to update
    while (!updatedVars.empty()) {

        //To track if an equation has already been updated in this round
        vector<char> eqsUpdated(eqs.size(), 0);

        //Make a copy of what vars are updated
        //we will clear and set the old structure
        set<uint32_t> oldUpdatedVars = updatedVars;
        updatedVars.clear();

        for(set<uint32_t>::const_iterator
            it = oldUpdatedVars.begin(), end = oldUpdatedVars.end()
            ; it != end
            ; it++
        ) {
            assert(occur.size() > *it);

            //We will update the occur now, so make a backup first
            const vector<size_t> backupOccur = occur[*it];

            //Go through all polynomials that could be touched by
            //the value update of this variable
            for(vector<size_t>::const_iterator
                it2 = backupOccur.begin(), end2 = backupOccur.end()
                ; it2 != end2
                ; it2++
            ) {
                const size_t index = *it2;
                assert(eqs.size() > index);

                //This poly has already been updted in this round
                if (eqsUpdated[index])
                    continue;

                eqsUpdated[index] = 1;
                simplifyPolyonomial(eqs[index], index, replace);
            }
        }
    }

    removeEmptyEquations();
    check_simplified_polys_contain_no_set_vars();
}

void ANF::check_simplified_polys_contain_no_set_vars() const
{
    for(vector<BoolePolynomial>::const_iterator
        it = eqs.begin(), end = eqs.end()
        ; it != end
        ; it++
    ) {
        const BoolePolynomial& eq = *it;
        for(BooleMonomial::const_iterator
            vit = eq.usedVariables().begin(), vend = eq.usedVariables().end()
            ; vit != vend
            ; vit++
        ) {
            const uint32_t var = *vit;
            if (value(var) != l_Undef) {
                cout
                << "ERROR: Variable "
                << var
                << " is inside equation "
                << eq
                << " even though its value is "
                << value(var)
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
    for(size_t i = 0; i < eqs.size(); i++) {
        const BoolePolynomial& poly = eqs[i];

        //If equation is constant zero, don't add to new_eqs
        //and update the occur_delta for all future equations
        if (poly.isConstant() && !poly.isOne()) {
            for(size_t i2 = i; i2 < eqs.size(); i2++) {
                occur_delta[i2]++;
            }
            continue;
        }

        //Not constant zero, so add
        new_eqs.push_back(poly);
    }

    //Go through each variable occurance
    for(vector<vector<size_t> >::iterator
        it = occur.begin(), end = occur.end()
        ; it != end
        ; it++
    ) {

        //The indexes of the equations have changed. Update them.
        for(vector<size_t>::iterator
            it2 = it->begin(), end2 = it->end()
            ; it2 != end2
            ; it2++
        ) {
            assert(*it2 >= occur_delta[*it2]);
            *it2 -= occur_delta[*it2];
        }
    }

    eqs = new_eqs;
}

bool ANF::evaluate(const vector<lbool>& vals) const
{
    bool ret = true;
    for(vector<BoolePolynomial>::const_iterator it = eqs.begin(), end = eqs.end(); it != end; it++) {
        lbool lret = evaluatePoly(*it, vals);
        assert(lret != l_Undef);

        //OOps, grave bug in implmenetation
        if (lret != l_True) {
            cout
            << "Internal ERROR! Solution doesn't satisfy eq '"
            << *it << "'"
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

/**
 * @short Checks if occurrance list is (partially) OK
**/
void ANF::checkOccur() const
{
    for(vector<vector<size_t> >::const_iterator
        it = occur.begin(), end = occur.end()
        ; it != end
        ; it++
    ) {
        for(vector<size_t>::const_iterator
            it2 = it->begin(), end2 = it->end()
            ; it2 != end2
            ; it2++
        ) {
            assert(*it2 < eqs.size());
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
    simplify(true);
}

void ANF::extractVariables(
    const size_t from
    , const size_t to
    , const vector<lbool>* sol
) const {
    uint64_t ret = 0;
    bool unknown_inside = false;
    for(size_t i = from, at = 0; i <= to; i++, at++) {
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
            ret |= ((uint64_t)1) << (to-from-1)-at;
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

    for(size_t i = 0; i < unknown.size(); i++) {
        uint32_t oldVar = unknown[i];
        vector<uint32_t> replaces = replacer->getReplacesVars(oldVar);

        //Replaces itself and others
        oldToNewMap[oldVar] = i;
        for(uint32_t var: replaces) {
            oldToNewMap[var] = i;
        }

        newToOldMap[i] = oldVar;
    }

    BoolePolyRing* newring = new BoolePolyRing(unknown.size());
    ANF* newanf = new ANF(newring, config);

    for(vector<BoolePolynomial>::const_iterator
        it = eqs.begin(), end = eqs.end()
        ; it != end
        ; it++
    ) {
        BoolePolynomial newpoly(*newring);

        //Update poly
        for(BoolePolynomial::const_iterator
            it2 = it->begin(), end2 = it->end()
            ; it2 != end2
            ; it2++
        ) {
            BooleMonomial newm(*newring);

            const BooleMonomial& m = *it2;
            for(BooleMonomial::const_iterator
                it3 = m.begin(), end3 = m.end()
                ; it3 != end3
                ; it3++
            ) {
                uint32_t var = *it3;
                assert(oldToNewMap.size() > var);
                assert(oldToNewMap[var] != std::numeric_limits<uint32_t>::max());
                uint32_t newVar = oldToNewMap[var];
                newm *= BooleVariable(newVar, *newring);
            }
            newpoly += newm;
        }


        newanf->addBoolePolynomial(newpoly);
    }

    return newanf;
}

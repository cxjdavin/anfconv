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

#include <boost/program_options.hpp>
namespace po = boost::program_options;

#include "anf.h"
#include "cnf.h"
#include "gaussjordan.h"
#include <fstream>
#include <sys/wait.h>
#include "time_mem.h"
#include <fstream>
#include "satsolve.h"
#include "simplifybysat.h"
#include "replacer.h"
#include "GitSHA1.h"
#include <memory>
#include <deque>

//#define DEBUG_EXTRACTION
using std::cout;
using std::cerr;
using std::endl;
using std::string;
using std::deque;

string anf_input;
string anf_output;
string cnf_output;
string programName;

//Writing options
bool writeANF;
bool writeCNF;

//Solving options
bool doSolveSAT; //Solve using CryptoMiniSat

//Dependency
int renumber_ring_vars;

//How to simplify
bool doANFSimplify;
bool doGJSimplify;
bool doXLSimplify;
bool doElimLinSimplify;
bool doSATSimplify;

//Parameters
ConfigData config;
uint64_t numConfl;
vector<string> extractString;

void parseOptions(int argc, char *argv[])
{
    // Declare the supported options.
    po::options_description generalOptions("Allowed options");
    generalOptions.add_options()
    ("help,h", "produce help message")
    ("version", "print version number and exit")
    ("read,r", po::value(&anf_input)
        , "Read ANF from this file")
    ("anfwrite,a", po::value(&anf_output)
        , "Write ANF output to file")
    ("cnfwrite,c", po::value(&cnf_output)
        , "Write CNF output to file")
    ("solvesat,s", po::bool_switch(&doSolveSAT)
        , "Solve with SAT solver")
    ("printdeg", po::value(&config.max_degree_poly_to_print)->default_value(-1)
        , "Print only final polynomials of degree lower or equal to this. -1 means print all")
    ("karn", po::value(&config.useKarn)->default_value(config.useKarn)
        , "Use Karnaugh table minimisation")
    ("program,p", po::value(&programName)->default_value("/usr/local/bin/cryptominisat")
        , "SAT solver to use with full path")
    ("verbosity,v", po::value(&config.verbosity)->default_value(1)
        , "Verbosity setting (0 = silent)")
    ("dump,d", po::bool_switch(&config.writePNG)
         , "Dump XL's and linearization's matrixes as PNG files")
    ("anfsimp", po::bool_switch(&doANFSimplify)
         , "Simply ANF before doing anything")
    ("gjsimp", po::bool_switch(&doGJSimplify)
         , "Simplify using GaussJordan")
    ("xlsimp", po::bool_switch(&doXLSimplify)
         , "Simplify using XL (performs GaussJordan internally)")
    ("elimlinsimp", po::bool_switch(&doElimLinSimplify)
         , "Simplify using ElimLin (performs GaussJordan internally)")
    ("satsimp", po::bool_switch(&doSATSimplify)
         , "Simplify using SAT")
    ("confl", po::value<uint64_t>(&numConfl)->default_value(20000)
        , "Conflict limit for built-in SAT solver")
    ("cutnum", po::value(&config.cutNum)->default_value(config.cutNum)
        , "Cutting number when not using XOR clauses")
    ("extract,e", po::value(&extractString)->multitoken()
        , "Extract the values of these variables as binary string from final ANF. \
             Must be like '10-20' for extracting x10...x20")
    ("revar", po::value(&renumber_ring_vars)->default_value(0)
        , "Minimise (renumber) ANF before attempting dependency calculation. Reduces ring size")

    ;

    po::positional_options_description p;
    p.add("read", -1);

    po::variables_map vm;
    po::options_description cmdline_options;
    cmdline_options
    .add(generalOptions)
    ;

    try {
        po::store(
            po::command_line_parser(argc, argv)
            .options(cmdline_options)
            .positional(p).run()
            , vm
        );

        if (vm.count("help"))
        {
            cout << generalOptions << endl;
            exit(0);
        }

        po::notify(vm);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::unknown_option> >& c
    ) {
        cout << "Some option you gave was wrong. Please give '--help' to get help" << endl;
        cout << "Unkown option: " << c.what() << endl;
        exit(-1);
    } catch (boost::bad_any_cast &e) {
        cerr << e.what() << endl;
        exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::invalid_option_value> > what
    ) {
        cerr
        << "Invalid value '" << what.what() << "'"
        << " given to option '" << what.get_option_name() << "'"
        << endl;

        exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::multiple_occurrences> > what
    ) {
        cerr
        << "Error: " << what.what() << " of option '"
        << what.get_option_name() << "'"
        << endl;

        exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::required_option> > what
    ) {
        cerr
        << "You forgot to give a required option '"
        << what.get_option_name() << "'"
        << endl;

        exit(-1);
    }

    if (vm.count("version")) {
        cout << "anfconv " << get_git_version() << endl;
        exit(0);
    }

    //Writing methods
    if (vm.count("anfwrite")) {
        writeANF = true;
    }
    if (vm.count("cnfwrite")) {
        writeCNF = true;
    }


    if (config.cutNum < 3 || config.cutNum > 10) {
        cout
        << "ERROR! For sanity, cutting number must be between 3 and 10"
        << endl;

        exit(-1);
    }

    if (!vm.count("read")) {
        cout
        << "You must give an ANF file to read in"
        << endl;

        exit(-1);
    }
}

std::pair<uint32_t, uint32_t> get_var_range(const string& extractString, uint32_t max_var)
{
    const size_t pos = extractString.find("-");
    if (pos == string::npos) {
        std::cerr
        << "ERROR: you gave a variable range but your string doesn't contain '-'"
        << endl;
        exit(-1);
    }

    //Extract TO and FROM
    int from;
    int to;
    try {
        from = boost::lexical_cast<int>(extractString.substr(0,pos));
        assert(extractString[pos] == '-');
        to = boost::lexical_cast<int>(extractString.substr(pos+1,extractString.size()-pos-1));
    } catch (boost::bad_lexical_cast& b) {
        cout
        << "ERROR: either TO or FROM given to --extract couldn't be converted to integer: "
        << endl
        << b.what()
        << " -- maybe not an integer?"
        << endl;

        exit(-1);
    }

    //User feedback
    cout
    << "Extracting values "
    << from << " - " << to
    << endl;

    //Sanity checks
    if (from < 0 || to < 0)  {
        std::cerr
        << "ERROR: During extraction, the FROM or the TO parameter is smaller than 0"
        << endl;
        exit(-1);
    }

    if (to < from) {
        std::cerr
        << "ERROR: During extraction, you gave the FROM value to be larger than the TO value"
        << endl;
        exit(-1);
    }

    if (max_var < (size_t)to) {
        std::cerr
        << "ERROR: During extraction, the TO you gave is higher than the number of variables in the ANF"
        << "( " << max_var << ")"
        << endl;
        exit(-1);
    }

    return std::make_pair(from, to);
}

uint32_t get_var(const string var_num, const uint32_t max_var)
{
    uint32_t var = boost::lexical_cast<int>(var_num);
    assert(var < max_var);
    return var;
}

size_t get_ringsize(const string anf_filename)
{
    BoolePolyRing* ring = new BoolePolyRing(1);
    ANF* anf = new ANF(ring, config);
    const size_t ring_size = anf->readFile(anf_filename, false);
    cout << "--> Needed ring size is " << ring_size+1 << endl;

    return ring_size;
}

void simplify(ANF* anf, const ANF& orig_anf)
{
    if (config.verbosity>=1) {
        cout << "Simple simplifying of ANF..." << endl
             << "ANF simp: " << doANFSimplify << endl
             << "GJ simp: " << doGJSimplify << endl
             << "XL simp: " << doXLSimplify << endl
             << "EL simp: " << doElimLinSimplify << endl
             << "SAT simp: " << doSATSimplify << endl;
    }

    bool changed = true;
    uint32_t numIters = 0;
    double myTime = cpuTime();
    while (changed) {
        changed = false;

        uint64_t prev_set_vars = anf->getNumSetVars();
        uint64_t prev_eq_num = anf->size();
        uint64_t prev_monom_in_eq = anf->numMonoms();
        uint64_t prev_deg = anf->deg();
        uint64_t prev_simp_xors = anf->getNumSimpleXors();
        uint64_t prev_replaced_vars = anf->getNumReplacedVars();

        // Basic propagation
        anf->propagate();

        // Apply ANF simplification
        if (doANFSimplify) {
            anf->simplify();
            anf->propagate();
        }

        // Apply Gauss Jordan simplification
        if (doGJSimplify) {
            // Add and print new truths found
            vector<BoolePolynomial> newTruths;
            GaussJordan gj(anf->getEqs(), anf->getRing(), config, -1);
            changed |= gj.run(newTruths);
            for(BoolePolynomial poly : newTruths) {
                anf->addBoolePolynomial(poly);
            }
            anf->propagate();
        }

        // Apply XL simplification (includes Gauss Jordan)
        if (doXLSimplify) {
            // For now, only extend by degree 1 monomials
            vector<BoolePolynomial> equations;
            for (const BoolePolynomial& poly : anf->getEqs()) {
                equations.push_back(poly);
            }
            for (unsigned long i = 0; i < anf->getRing().nVariables(); ++i) {
                BooleVariable v = anf->getRing().variable(i);
                for (const BoolePolynomial& poly : anf->getEqs()) {
                    equations.push_back(BoolePolynomial(v * poly));
                }
            }

            // Add and print new truths found
            vector<BoolePolynomial> newTruths;
            GaussJordan gj(equations, anf->getRing(), config, -1);
            changed |= gj.run(newTruths);
            for(BoolePolynomial poly : newTruths) {
                anf->addBoolePolynomial(poly);
            }
            anf->propagate();
        }

        // Apply ElimLin simplification (includes Gauss Jordan)
        if (doElimLinSimplify) {
            bool fixed_point = false;
            while (!fixed_point) {
                cout << *anf << endl;
                bool eliminated_something = anf->eliminate_linear();
                cout << *anf << endl;
                cout << "EL DONE\n";

                // Add and print new truths found
                vector<BoolePolynomial> newTruths;
                GaussJordan gj(anf->getEqs(), anf->getRing(), config, -1);
                bool new_gj_truth = gj.run(newTruths);
                for(BoolePolynomial poly : newTruths) {
                    anf->addBoolePolynomial(poly);
                }
                cout << "GAUSS DONE\n";

                changed |= (eliminated_something || new_gj_truth);
                fixed_point = (!eliminated_something && !new_gj_truth);
            }

            anf->propagate();
            cout << *anf << endl;
        }

        // Apply SAT simplification (run CMS, then extract learnt clauses)
        if (doSATSimplify) {
            SimplifyBySat simpsat(*anf, orig_anf, config, numConfl);
            changed |= simpsat.simplify();
            anf->propagate();
        }

        uint64_t set_vars = anf->getNumSetVars();
        uint64_t eq_num = anf->size();
        uint64_t monom_in_eq = anf->numMonoms();
        uint64_t deg = anf->deg();
        uint64_t simp_xors = anf->getNumSimpleXors();
        uint64_t replaced_vars = anf->getNumReplacedVars();

        changed |= (set_vars != prev_set_vars ||
                    eq_num != prev_eq_num ||
                    monom_in_eq != prev_monom_in_eq ||
                    deg != prev_deg ||
                    simp_xors != prev_simp_xors ||
                    replaced_vars != prev_replaced_vars);
        numIters++;
    }
}

void write_anf(ANF* anf)
{
    std::ofstream ofs;
    ofs.open(anf_output.c_str());
    if (!ofs) {
        std::cerr
        << "Error opening file \"" << anf_output << "\" for writing"
        << endl;
        exit(-1);
    }

    ANF* newanf = NULL;
    if (renumber_ring_vars) {
        anf->preferLowVars();
        vector<uint32_t> oldToNew;
        vector<uint32_t> newToOld;
        newanf = anf->minimise(oldToNew, newToOld);
    } else {
        newanf = anf;
    }

    //Write to file
    ofs << *newanf << endl;

    if (renumber_ring_vars) {
        delete newanf;
    }
}

void solve_by_sat(const ANF* anf, const ANF& orig_anf)
{
    double myTime = cpuTime();

    CNF cnf(*anf, config);
    cnf.init();
    cnf.addAllEquations();

    cout << "c ---- CNF stats -----" << endl;
    cout << "c CNF conversion time  : " << (cpuTime() - myTime) << endl;
    cnf.print_stats();

    if (writeCNF) {
        std::ofstream ofs;
        ofs.open(cnf_output.c_str());
        if (!ofs) {
            cout << "Error opening file \""
            << cnf_output
            << "\" for writing" << endl;
            exit(-1);
        }
        ofs << cnf << endl;
        ofs.close();
    }

    if (doSolveSAT) {
        SATSolve solver(config.verbosity, programName);
        vector<lbool> sol = solver.solveCNF(orig_anf, *anf, cnf);

        if (config.verbosity >= 1) {
            cout << "c CPU time unknown " << endl;
        }

        if (!sol.empty()) {
            for(const string str :extractString) {
                std::pair<uint32_t, uint32_t> range = get_var_range(str, orig_anf.getRing().nVariables());
                anf->extractVariables(range.first, range.second, &sol);
            }
        }
    }
}

void perform_all_operations(const string anf_filename) {
    const size_t ring_size = get_ringsize(anf_filename);
    BoolePolyRing* ring = new BoolePolyRing(ring_size + 1);
    ANF* anf = new ANF(ring, config);
    anf->readFile(anf_filename, true);

    if (config.verbosity >= 1) {
        anf->printStats(config.verbosity);
    }

    //Simplification(s), recursively
    ANF orig_anf(*anf);
    simplify(anf, orig_anf);
    cout << *anf << endl;

    //Writing simplified ANF
    if (writeANF) {
        write_anf(anf);
    }

    //We need to extract data
    if (!extractString.empty()) {
        if (!anf->getOK()) {
            //If UNSAT, there is no solution to extract
            cout << "UNSAT, so no solution to extract" << endl;
        } else {
            //Go through each piece of data that needs extraction
            for(const string str: extractString) {
                std::pair<uint32_t, uint32_t> range = get_var_range(str, orig_anf.getRing().nVariables());
                anf->extractVariables(range.first, range.second);
            }
        }
    }

    //CNF conversion and solving
    if (doSolveSAT || writeCNF) {
        solve_by_sat(anf, orig_anf);
    }
}

int main(int argc, char *argv[])
{
    parseOptions(argc, argv);
    if (anf_input.length() == 0) {
        cerr << "ERROR: you must provide an ANF input file" << endl;
    }
    perform_all_operations(anf_input);
    cout << endl;

    return 0;
}

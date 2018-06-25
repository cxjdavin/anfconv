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
bool printSimpANF;
bool writeANF;
bool writeCNF;

//Solving options
bool doSolveSAT; //Solve using CryptoMiniSat

//Dependency
int renumber_ring_vars;

//How to simplify
bool doAllSimplify;
bool doANFSimplify;
bool doGJSimplify;
bool doXLSimplify;
bool doELSimplify;
bool doSATSimplify;

//Parameters
ConfigData config;
uint32_t xl_deg;
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
    ("printsimp", po::bool_switch(&printSimpANF)
        , "Print simplified ANF. Default = false (for cleaner terminal output)")
    ("dump,d", po::bool_switch(&config.writePNG)
         , "Dump XL's and linearization's matrixes as PNG files")
    ("allsimp", po::bool_switch(&doAllSimplify)
         , "Apply all simplification tricks")
    ("anfsimp", po::bool_switch(&doANFSimplify)
         , "Simplify ANF before doing anything")
    ("gjsimp", po::bool_switch(&doGJSimplify)
         , "Simplify using GaussJordan")
    ("xlsimp", po::bool_switch(&doXLSimplify)
         , "Simplify using XL (performs GaussJordan internally)")
    ("xldeg", po::value<uint32_t>(&xl_deg)->default_value(1)
         , "Expansion degree for XL algorithm. Default = 1 (for now we only support up to xldeg = 3)")
    ("elsimp", po::bool_switch(&doELSimplify)
         , "Simplify using ElimLin (performs GaussJordan internally)")
    ("satsimp", po::bool_switch(&doSATSimplify)
         , "Simplify using SAT")
    ("confl", po::value<uint64_t>(&numConfl)->default_value(100000)
        , "Conflict limit for built-in SAT solver. Default = 100000")
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
    cout << "c Needed ring size is " << ring_size+1 << endl;
    return ring_size;
}

// Returns n choose r
// Note: Assume no overflow
uint32_t nCr(uint32_t n, uint32_t r) {
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

void simplify(ANF* anf, const ANF& orig_anf)
{
    double loopStartTime = cpuTime();

    if (doAllSimplify) {
        doANFSimplify = true;
        doGJSimplify = true;
        doXLSimplify = true;
        doELSimplify = true;
        doSATSimplify = true;
    }
    if (config.verbosity>=1) {
        cout << "c Begin simplifying of ANF..." << endl
             << "c ANF simp: " << doANFSimplify << endl
             << "c GJ simp: " << doGJSimplify << endl
             << "c XL simp (deg = " << xl_deg << "): " << doXLSimplify << endl
             << "c EL simp: " << doELSimplify << endl
             << "c SAT simp (confl limit = " << numConfl << "): " << doSATSimplify << endl;
    }

    // Perform initial propagation to avoid needing >= 2 iterations
    anf->propagate();

    uint32_t numIters = 0;
    bool changed = true;
    while (changed) {
        changed = false;

        // Apply Gauss Jordan simplification
        if (doGJSimplify) {
            double startTime = cpuTime();
            int num_learnt = 0;

            long long num_cells = anf->size() * anf->numUniqueMonoms(anf->getEqs());
            if (num_cells > 1000000000) {
                cout << "c Matrix has over 1 billion cells. Skip GJE\n";
            } else {
                GaussJordan gj(anf->getEqs(), anf->getRing());
                vector<BoolePolynomial> truths_from_gj;
                gj.run(truths_from_gj);
                for(BoolePolynomial poly : truths_from_gj) {
                    num_learnt += anf->addLearntBoolePolynomial(poly);
                }
            }

            if (config.verbosity >= 1) {
                cout << "c [Gauss Jordan] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply XL simplification (includes Gauss Jordan)
        if (doXLSimplify) {
            double startTime = cpuTime();
            int num_learnt = 0;

            if (xl_deg > 3) {
               cout << "c We only currently support up to xldeg = 3" << endl;
               assert(false);
            }

            int multiplier = 0;
            for (uint32_t d = 0; d <= xl_deg; ++d) {
                // Add (n choose d)
                multiplier += nCr(anf->getRing().nVariables(), d);
            }
            if ((double) anf->size() * multiplier > 1000000000 / anf->getRing().nVariables()) {
                cout << "c Matrix has over 1 billion cells. Skip XL\n";
            } else {
                vector<BoolePolynomial> equations;
                for (const BoolePolynomial& poly : anf->getEqs()) {
                    equations.push_back(poly);
                }

                // ugly hack
                // To do: Use an efficient implementation of "nVars choose xl_deg"
                //        from http://howardhinnant.github.io/combinations.html?
                unsigned long nVars = anf->getRing().nVariables();
                if (xl_deg >= 1) {
                    for (unsigned long i = 0; i < nVars; ++i) {
                        BooleVariable v = anf->getRing().variable(i);
                        for (const BoolePolynomial& poly : anf->getEqs()) {
                            equations.push_back(BoolePolynomial(v * poly));
                        }
                    }
                }
                if (xl_deg >= 2) {
                    for (unsigned long i = 0; i < nVars; ++i) {
                        for (unsigned long j = i+1; j < nVars; ++j) {
                            BooleVariable v1 = anf->getRing().variable(i);
                            BooleVariable v2 = anf->getRing().variable(j);
                            for (const BoolePolynomial& poly : anf->getEqs()) {
                                equations.push_back(BoolePolynomial(v1 * v2 * poly));
                            }
                        }
                    }
                }
                if (xl_deg >= 3) {
                    for (unsigned long i = 0; i < nVars; ++i) {
                        for (unsigned long j = i+1; j < nVars; ++j) {
                            for (unsigned long k = j+1; k < nVars; ++k) {
                                BooleVariable v1 = anf->getRing().variable(i);
                                BooleVariable v2 = anf->getRing().variable(j);
                                BooleVariable v3 = anf->getRing().variable(k);
                                for (const BoolePolynomial& poly : anf->getEqs()) {
                                    equations.push_back(BoolePolynomial(v1 * v2 * v3 * poly));
                                }
                            }
                        }
                    }
                }
                GaussJordan gj(equations, anf->getRing());
                vector<BoolePolynomial> truths_from_gj;
                gj.run(truths_from_gj);
                for(BoolePolynomial poly : truths_from_gj) {
                    num_learnt += anf->addLearntBoolePolynomial(poly);
                }
            }

            if (config.verbosity >= 1) {
                cout << "c [XL] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply ElimLin simplification (includes Gauss Jordan)
        if (doELSimplify) {
            double startTime = cpuTime();
            int num_learnt = anf->elimlin();
            if (config.verbosity >= 1) {
                cout << "c [ElimLin] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply SAT simplification (run CMS, then extract learnt clauses)
        if (doSATSimplify) {
            double startTime = cpuTime();
            SimplifyBySat simpsat(*anf, orig_anf, config, numConfl);
            int num_learnt = simpsat.simplify();
            if (config.verbosity >= 1) {
                cout << "c [Cryptominisat] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply ANF simplification
        // Do not update changed if using ANF simplification
        if (doANFSimplify) {
            anf->simplify();
            anf->propagate();
        } else {
            uint64_t initial_set_vars = anf->getNumSetVars();
            uint64_t initial_eq_num = anf->size();
            uint64_t initial_monom_in_eq = anf->numMonoms();
            uint64_t initial_deg = anf->deg();
            uint64_t initial_simp_xors = anf->getNumSimpleXors();
            uint64_t initial_replaced_vars = anf->getNumReplacedVars();
            anf->propagate();
            changed |= (anf->getNumSetVars() != initial_set_vars);
            changed |= (anf->size() != initial_eq_num);
            changed |= (anf->numMonoms() != initial_monom_in_eq);
            changed |= (anf->deg() != initial_deg);
            changed |= (anf->getNumSimpleXors() != initial_simp_xors);
            changed |= (anf->getNumReplacedVars() != initial_replaced_vars);
        }
        numIters++;
    }
    if (config.verbosity >= 1) {
        cout << "c [Tool terminated after " << numIters << " iteration(s) in "
             << (cpuTime() - loopStartTime) << " seconds.]" << endl;
    }
}

void write_anf(ANF* anf)
{
    std::ofstream ofs;
    ofs.open(anf_output.c_str());
    if (!ofs) {
        std::cerr
        << "c Error opening file \"" << anf_output << "\" for writing"
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
            cout << "c Error opening file \""
            << cnf_output
            << "\" for writing" << endl;
            exit(-1);
        }
        for(size_t i = 0; i < anf->getRing().nVariables(); i++) {
            //BooleVariable v(i, anf->getRing());
            Lit l = anf->getReplaced(i);
            BooleVariable v(l.var(), anf->getRing());
            ofs << "c MAP " << i << " = " << cnf.getVarForMonom(v) << endl;
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
    double parseStartTime = cpuTime();
    const size_t ring_size = get_ringsize(anf_filename);
    BoolePolyRing* ring = new BoolePolyRing(ring_size + 1);
    ANF* anf = new ANF(ring, config);
    anf->readFile(anf_filename, true);
    if (config.verbosity >= 1) {
        cout << "c Input ANF parsed in "
             << (cpuTime() - parseStartTime) << " seconds." << endl;
        anf->printStats(config.verbosity);
    }

    // Perform simplifications
    ANF orig_anf(*anf);
    simplify(anf, orig_anf);
    if (printSimpANF) {
        cout << *anf << endl;
    }

    // Write simplified ANF
    if (writeANF) {
        write_anf(anf);
    }

    //We need to extract data
    if (!extractString.empty()) {
        if (!anf->getOK()) {
            //If UNSAT, there is no solution to extract
            cout << "c UNSAT, so no solution to extract" << endl;
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

    if (config.verbosity >= 1) {
        anf->printStats(config.verbosity);
    }
}

int main(int argc, char *argv[])
{
    parseOptions(argc, argv);
    if (anf_input.length() == 0) {
        cerr << "c ERROR: you must provide an ANF input file" << endl;
    }
    perform_all_operations(anf_input);
    cout << endl;

    return 0;
}

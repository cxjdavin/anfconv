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

#include <boost/program_options.hpp>
namespace po = boost::program_options;

#include <deque>
#include <fstream>
#include <memory>
#include <sys/wait.h>

#include "anf.h"
#include "cnf.h"
#include "gaussjordan.h"
#include "GitSHA1.h"
#include "replacer.h"
#include "satsolve.h"
#include "simplifybysat.h"
#include "time_mem.h"

using std::cout;
using std::cerr;
using std::endl;
using std::string;
using std::deque;

ConfigData config;

void parseOptions(int argc, char *argv[]) {
    // Store executed arguments to print in output comments
    for (int i=1 ; i < argc; i++) {
        config.executedArgs.append(string(argv[i]).append(" "));
    }

    // Declare the supported options.
    po::options_description generalOptions("Allowed options");
    generalOptions.add_options()
    ("help,h", "produce help message")
    ("version", "print version number and exit")
    // Input/Output
    ("anfread", po::value(&config.anfInput), "Read ANF from this file")
    ("cnfread", po::value(&config.cnfInput), "Read CNF from this file")
    ("anfwrite", po::value(&config.anfOutput), "Write ANF output to file")
    ("cnfwrite", po::value(&config.cnfOutput), "Write CNF output to file")
    ("printfinal", po::bool_switch(&config.printProcessedANF)->default_value(false),
        "Print final processed ANF. Default = false (for cleaner terminal output)")
    ("verbosity,v", po::value<uint32_t>(&config.verbosity)->default_value(1),
        "Verbosity setting (0 = silent)")
    // CNF conversion
    ("cutnum", po::value<uint32_t>(&config.cutNum)->default_value(4),
        "Cutting number when not using XOR clauses")
    ("karn", po::value(&config.maxKarnTableSize)->default_value(8),
        "Sets Karnaugh map dimension during CNF conversion")
    // Processes
    ("nolimiters", po::bool_switch(&config.nolimiters)->default_value(false),
        "Disable limiters on simplification processes.")
    ("nodefault", po::bool_switch(&config.nodefault)->default_value(false),
        "Disables default setting. You now have to manually switch on simplification processes.")
    ("gjsimp", po::bool_switch(&config.doGJSimplify)->default_value(false),
        "Simplify using GaussJordan")
    ("xlsimp", po::bool_switch(&config.doXLSimplify)->default_value(false),
        "Simplify using XL (performs GaussJordan internally)")
    ("xldeg", po::value<uint32_t>(&config.xlDeg)->default_value(1),
        "Expansion degree for XL algorithm. Default = 1 (for now we only support up to xldeg = 3)")
    ("elsimp", po::bool_switch(&config.doELSimplify)->default_value(false),
        "Simplify using ElimLin (performs GaussJordan internally)")
    ("satsimp", po::bool_switch(&config.doSATSimplify)->default_value(false),
        "Simplify using SAT")
    ("confl", po::value<uint64_t>(&config.numConfl)->default_value(100000),
        "Conflict limit for built-in SAT solver. Default = 100000")
    // Solve processed CNF
    ("solvesat,s", po::bool_switch(&config.doSolveSAT), "Solve with SAT solver")
    ("solverexe,e", po::value(&config.solverExe)->default_value("/usr/local/bin/cryptominisat"),
        "Solver executable (for SAT solving on processed CNF)")
    ("solvewrite,o", po::value(&config.solutionOutput), "Write solver output to file")
    ;

    po::variables_map vm;
    po::options_description cmdline_options;
    cmdline_options.add(generalOptions);

    try {
        po::store(
            po::command_line_parser(argc, argv)
            .options(cmdline_options)
            .run()
            , vm
        );
        if (vm.count("help")) {
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
        cout << "INDRA " << get_git_version() << endl;
        exit(0);
    }

    // I/O checks
    if (vm.count("anfread")) {
        config.readANF = true;
    }
    if (vm.count("cnfread")) {
        config.readCNF = true;
    }
    if (vm.count("anfwrite")) {
        config.writeANF = true;
    }
    if (vm.count("cnfwrite")) {
        config.writeCNF = true;
    }
    if (!config.readANF && !config.readCNF) {
        cout << "You must give an ANF/CNF file to read in\n";
        exit(-1);
    }
    if (config.readANF && config.readCNF) {
        cout << "You cannot give both ANF/CNF files to read in\n";
        exit(-1);
    }

    // Config checks
    if (config.cutNum < 3 || config.cutNum > 10) {
        cout << "ERROR! For sanity, cutting number must be between 3 and 10\n";
        exit(-1);
    }
    if (config.maxKarnTableSize > 20) {
        cout << "ERROR! For sanity, max Karnaugh table size is at most 20\n";
        exit(-1);
    }
    if (config.xlDeg > 3) {
        cout << "ERROR! We only currently support up to xldeg = 3\n";
        exit(-1);
    }
    if (config.doSolveSAT && !vm.count("solvewrite")) {
        cout << "ERROR! Provide a output file for the solving of the processed CNF\n";
        exit(-1);
    }
}

ANF* read_anf() {
    // Find out maxVar in input ANF file
    BoolePolyRing* ring_tmp = new BoolePolyRing(1);
    ANF* anf_tmp = new ANF(ring_tmp, config);
    size_t maxVar = anf_tmp->readFile(config.anfInput, false);

    // Construct ANF
    // ring size = maxVar + 1, because ANF variables start from x0
    BoolePolyRing* ring = new BoolePolyRing(maxVar + 1);
    ANF* anf = new ANF(ring, config);
    anf->readFile(config.anfInput, true);
    return anf;
}

ANF* read_cnf() {
    // Find out maxVar in input CNF file
    size_t maxVar = 0;
    std::ifstream ifs;
    std::string temp, x;
    ifs.open(config.cnfInput.c_str());
    if (!ifs) {
        cout << "Problem opening file: " << config.cnfInput << " for reading\n";
        exit(-1);
    }
    while(std::getline(ifs, temp)) {
        if (temp.length() == 0 || temp[0] == 'p' || temp[0] == 'c') {
            continue;
        } else {
            std::istringstream iss(temp);
            while(iss) {
                iss >> x;
                maxVar = std::max(maxVar, (size_t) abs(stoi(x)));
            }
        }
    }

    // Reset file stream
    ifs.clear();
    ifs.seekg(0, ifs.beg);

    // Construct ANF
    // ring size = maxVar, because CNF variables start from 1
    BoolePolyRing* ring = new BoolePolyRing(maxVar);
    ANF* anf = new ANF(ring, config);
    while(std::getline(ifs, temp)) {
        if (temp.length() == 0 || temp[0] == 'p' || temp[0] == 'c') {
            continue;
        } else {
            BoolePolynomial poly(1, *ring);
            std::istringstream iss(temp);
            while(iss) {
                iss >> x;
                int v = stoi(x);
                if (v == 0) {
                    break;
                } else if (v > 0) {
                    poly *= (BooleConstant(1) + BooleVariable(abs(v)-1, *ring));
                } else if (v < 0) {
                    poly *= BooleVariable(abs(v)-1, *ring);
                }
            }
            anf->addBoolePolynomial(poly);
        }
    }
    return anf;
}

CNF* anf_to_cnf(const ANF* anf) {
    double convStartTime = cpuTime();
    CNF* cnf = new CNF(*anf, config);
    cnf->init();
    cnf->addAllEquations();
    if (config.verbosity >= 1) {
        cout << "c CNF conversion time  : " << (cpuTime() - convStartTime) << endl;
        cnf->printStats();
    }
    return cnf;
}

void write_anf(const ANF* anf) {
    std::ofstream ofs;
    ofs.open(config.anfOutput.c_str());
    if (!ofs) {
        std::cerr << "c Error opening file \"" << config.anfOutput << "\" for writing\n";
        exit(-1);
    } else {
        ofs << "c Executed arguments: " << config.executedArgs << endl;
        ofs << *anf << endl;
    }
    ofs.close();
}

void write_cnf(const ANF* anf) {
    CNF* cnf = anf_to_cnf(anf);
    std::ofstream ofs;
    ofs.open(config.cnfOutput.c_str());
    if (!ofs) {
        std::cerr << "c Error opening file \"" << config.cnfOutput << "\" for writing\n";
        exit(-1);
    } else {
        ofs << "c Executed arguments: " << config.executedArgs << endl;
        for(size_t i = 0; i < anf->getRing().nVariables(); i++) {
            Lit l = anf->getReplaced(i);
            BooleVariable v(l.var(), anf->getRing());
            ofs << "c MAP " << i << " = " << cnf->getVarForMonom(v) << endl;
        }
        ofs << *cnf << endl;
    }
    ofs.close();
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

void simplify(ANF* anf, const ANF& orig_anf) {
    double loopStartTime = cpuTime();
    if (!config.nodefault) {
        config.doGJSimplify = true;
        config.doXLSimplify = true;
        config.doELSimplify = true;
        config.doSATSimplify = true;
    }
    if (config.verbosity >= 1) {
        cout << "c --- Configuration ---\n"
             << "c GJ simp: " << config.doGJSimplify << endl
             << "c XL simp (deg = " << config.xlDeg << "): " << config.doXLSimplify << endl
             << "c EL simp: " << config.doELSimplify << endl
             << "c SAT simp (confl limit = " << config.numConfl << "): " << config.doSATSimplify << endl
             << "c Cut num: " << config.cutNum << endl
             << "c Karnaugh size: " << config.maxKarnTableSize << endl
             << "c --------------------\n";
    }

    // Perform initial propagation to avoid needing >= 2 iterations
    anf->propagate();

    uint32_t numIters = 0;
    bool changed = true;
    while (changed && anf->getOK()) {
        changed = false;

        // Apply Gauss Jordan simplification
        if (config.doGJSimplify) {
            double startTime = cpuTime();
            int num_learnt = 0;
            if (!config.nolimiters &&
                anf->size() * anf->numUniqueMonoms(anf->getEqs()) > 1000000000) {
                if (config.verbosity >= 3) {
                    cout << "c Matrix has over 1 billion cells. Skip GJE\n";
                }
            } else {
                GaussJordan gj(anf->getEqs(), anf->getRing(), config.verbosity);
                vector<BoolePolynomial> truths_from_gj;
                gj.run(truths_from_gj);
                for(BoolePolynomial poly : truths_from_gj) {
                    num_learnt += anf->addLearntBoolePolynomial(poly);
                }
            }
            if (config.verbosity >= 2) {
                cout << "c [Gauss Jordan] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply XL simplification (includes Gauss Jordan)
        if (config.doXLSimplify) {
            double startTime = cpuTime();
            int num_learnt = 0;
            int multiplier = 0;
            for (uint32_t d = 0; d <= config.xlDeg; ++d) {
                // Add (n choose d)
                multiplier += nCr(anf->getRing().nVariables(), d);
            }
            if (anf->size() == 0) {
                if (config.verbosity >= 3) {
                    cout << "c System is empty. Skip XL\n";
                }
            } else if (!config.nolimiters &&
                       (double) anf->size() * anf->getRing().nVariables() > 1000000000 / multiplier) {
                if (config.verbosity >= 3) {
                   cout << "c Matrix has over 1 billion cells. Skip XL\n"
                        << "c (This is a lower bound estimate assuming no change in numUniqueMonoms)\n";
                }
            } else {
                vector<BoolePolynomial> equations;
                for (const BoolePolynomial& poly : anf->getEqs()) {
                    equations.push_back(poly);
                }
                // Ugly hack
                // To do: Efficient implementation of "nVars choose xlDeg"
                //        e.g. http://howardhinnant.github.io/combinations.html?
                unsigned long nVars = anf->getRing().nVariables();
                if (config.xlDeg >= 1) {
                    for (unsigned long i = 0; i < nVars; ++i) {
                        BooleVariable v = anf->getRing().variable(i);
                        for (const BoolePolynomial& poly : anf->getEqs()) {
                            equations.push_back(BoolePolynomial(v * poly));
                        }
                    }
                }
                if (config.xlDeg >= 2) {
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
                if (config.xlDeg >= 3) {
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
                if (!config.nolimiters &&
                    (double) equations.size() > 1000000000 / anf->numUniqueMonoms(equations)) {
                    if (config.verbosity >= 3) {
                        cout << "c Matrix has over 1 billion cells. Skip XL\n";
                    }
                } else {
                    GaussJordan gj(equations, anf->getRing(), config.verbosity);
                    vector<BoolePolynomial> truths_from_gj;
                    gj.run(truths_from_gj);
                    for(BoolePolynomial poly : truths_from_gj) {
                        num_learnt += anf->addLearntBoolePolynomial(poly);
                    }
                }
            }
            if (config.verbosity >= 2) {
                cout << "c [XL] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply ElimLin simplification (includes Gauss Jordan)
        if (config.doELSimplify) {
            double startTime = cpuTime();
            int num_learnt = anf->elimLin();
            if (config.verbosity >= 2) {
                cout << "c [ElimLin] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

        // Apply SAT simplification (run CMS, then extract learnt clauses)
        if (config.doSATSimplify) {
            double startTime = cpuTime();
            SimplifyBySat simpsat(*anf, orig_anf, config);
            int num_learnt = simpsat.simplify();
            if (config.verbosity >= 2) {
                cout << "c [Cryptominisat] learnt " << num_learnt << " new facts in "
                     << (cpuTime() - startTime) << " seconds." << endl;
            }
            changed |= (num_learnt != 0);
        }

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
        numIters++;
    }
    if (config.verbosity >= 2) {
        cout << "c [Loop terminated after " << numIters << " iteration(s) in "
             << (cpuTime() - loopStartTime) << " seconds.]" << endl;
    }
}

void solve_by_sat(const ANF* anf, const ANF& orig_anf) {
    CNF* cnf = anf_to_cnf(anf);
    SATSolve solver(config.verbosity, config.solverExe);
    vector<lbool> sol = solver.solveCNF(orig_anf, *anf, *cnf);
    std::ofstream ofs;
    ofs.open(config.solutionOutput.c_str());
    if (!ofs) {
        std::cerr << "c Error opening file \"" << config.solutionOutput << "\" for writing\n";
        exit(-1);
    } else {
        size_t num = 0;
        ofs << "v ";
        for (const lbool lit : sol) {
            if (lit != l_Undef) {
                ofs << ((lit == l_True) ? "" : "-") << num << " ";
            }
            num++;
        }
        ofs << endl;
    }
    ofs.close();
}

int main(int argc, char *argv[]) {
    parseOptions(argc, argv);
    if (config.anfInput.length() == 0 && config.cnfInput.length() == 0) {
        cerr << "c ERROR: you must provide an ANF/CNF input file" << endl;
    }

    // Read from file
    ANF* anf;
    double parseStartTime = cpuTime();
    if (config.readANF) {
        anf = read_anf();
        if (config.verbosity >= 1) {
            cout << "c ANF Input parsed in "
                 << (cpuTime() - parseStartTime) << " seconds.\n";
        }
    }
    if (config.readCNF) {
        anf = read_cnf();
        if (config.verbosity >= 1) {
            cout << "c CNF Input parsed in "
                 << (cpuTime() - parseStartTime) << " seconds.\n";
        }
    }
    assert(anf != NULL);
    if (config.verbosity >= 1) {
        anf->printStats();
    }

    // Perform simplifications
    ANF orig_anf(*anf);
    simplify(anf, orig_anf);
    if (config.printProcessedANF) {
        cout << *anf << endl;
    }
    if (config.verbosity >= 1) {
        anf->printStats();
    }

    // Write to file
    if (config.writeANF) {
        write_anf(anf);
    }
    if (config.writeCNF) {
        write_cnf(anf);
    }

    // Solve processed CNF
    if (config.doSolveSAT) {
        solve_by_sat(anf, orig_anf);
    }

    if (config.verbosity >= 1) {
        cout << "c Indra completed in "
             << (cpuTime() - parseStartTime) << " seconds.\n";
    }
    return 0;
}

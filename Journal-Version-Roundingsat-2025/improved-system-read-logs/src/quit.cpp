/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2024, Jakob Nordström
Copyright (c) 2022-2024, Andy Oertel
Copyright (c) 2024, Marc Vinyals

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#include "quit.hpp"

#include <atomic>
#include <iostream>

#include "Logger.hpp"
#include "Solver.hpp"
#include "globals.hpp"

namespace rs::quit {

std::atomic_flag exiting = ATOMIC_FLAG_INIT;

void printSol(const Solver& solver, const std::vector<Lit>& sol) {
  printf("v");
  for (Var v = 1; v <= solver.getNbOrigVars(); ++v) printf(sol[v] > 0 ? " x%d" : " -x%d", v);
  printf("\n");
}

void printSolAsOpb(const Solver& solver, const std::vector<Lit>& sol) {
  for (Var v = 1; v <= solver.getNbOrigVars(); ++v) {
    if (sol[v] > 0)
      std::cout << "+1 x" << v << " >= 1 ;\n";
    else
      std::cout << "-1 x" << v << " >= 0 ;\n";
  }
}

void writeFinalStatus(std::ofstream* out, const bigint& bestObjVal, const std::string status) {
  *out << "\nnumDecisions: " << stats.NDECIDE << "\n";
  *out << "numConflicts: " << stats.NCONFL << "\n";
  *out << "numOfSolutionsFound: " << stats.NSOLS << "\n";
  *out << "numOfRestarts: " << stats.NRESTARTS << "\n";
  *out << "numOfCleanUps: " << stats.NCLEANUP << "\n";
  *out << "costOfBestSolution: " << (status!="UNSAT"? (status!="UNKNOWN"? bestObjVal : 0) : 0) << "\n";
  *out << "finalStatus: " << status << "\n";
  
  delete out;
}

void checkResults(const bigint& bestObjVal, const Result& r) {
  std::cout << "\ncheckResults.... " << std::endl;
  if (r.nDecisions == -1) {std::cout << "The solving is not completed!" << std::endl; return;}
  if(stats.NDECIDE != r.nDecisions) {
    std::cout << "numOfDecisions is not correct! Solver has " << stats.NDECIDE << ", but the stored #decisions is " << r.nDecisions << std::endl; exit(0);}
  if(stats.NCONFL != r.nConflicts) {
    std::cout << "numOfConflict is not correct! Solver has " << stats.NCONFL << ", but the stored #conflicts is " << r.nConflicts << std::endl; exit(0);}
  if(stats.NSOLS != r.nSolutionsFound) {
    std::cout << "numOfSolutionsFound is not correct! Solver has " << stats.NSOLS << ", but the stored #solutions is " << r.nSolutionsFound << std::endl; exit(0);}
  if(stats.NRESTARTS != r.nRestarts) {
    std::cout << "numOfRestarts is not correct! Solver has " << stats.NRESTARTS << ", but the stored #Restarts is " << r.nRestarts << std::endl; exit(0);}
  if(stats.NCLEANUP != r.nCleanups) {
    std::cout << "numOfCleanups is not correct! Solver has " << stats.NCLEANUP << ", but the stored #Cleanups is " << r.nCleanups << std::endl; exit(0);}
  if(stats.NSOLS != r.nSolutionsFound or (stats.NSOLS > 0 and bestObjVal != r.bestCost)) {
    std::cout << "costOfBestSolution is not correct! Solver has " << bestObjVal << ", but the stored bestCost is " << r.bestCost.str() << ", stats.NSOLS " << stats.NSOLS << ", stored is " << r.nSolutionsFound << std::endl; exit(0);}
}

void exit_SAT(const Env& env, const bigint& bestSoFar) {
  if (env.solver->read) checkResults(bestSoFar, env.solver->storedResult);
  if (exiting.test_and_set()) return;
  assert(env.solver->foundSolution());
  if (env.logger) {
    env.logger->solution(env.solver->lastSol);
    env.logger->sat(env.solver->lastSol);
  }
  if (options.verbosity.get() > 0) stats.print();
  if (env.opt) std::cout << "o " << bestSoFar << std::endl;
  puts("s SATISFIABLE");
  if (options.printSol) printSol(*env.solver, env.solver->lastSol);
  if (env.solver->write) writeFinalStatus(env.solver->einfo, bestSoFar, "SAT");
}

void exit_INDETERMINATE(const Env& env, const bigint& lb, const bigint& ub) {
  if (env.solver->read) checkResults(ub, env.solver->storedResult);
  if (exiting.test_and_set()) return;
  if (env.logger) {
    if (env.solver->foundSolution()) {
      env.logger->bounds(lb, ub, env.solver->lastSol);
    }
    else {
      env.logger->bounds(lb);
    }
  }
  if (options.verbosity.get() > 0) stats.print();
  if (env.solver->foundSolution()) {
    std::cout << "o " << ub << std::endl;
    puts("s SATISFIABLE");
    if (options.printSol) printSol(*env.solver, env.solver->lastSol);
    if (env.solver->write) writeFinalStatus(env.solver->einfo, ub, "SAT");
  } else {
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get())
      puts("s TIMELIMIT");
    else
      puts("s UNKNOWN");
    if (env.solver->write) writeFinalStatus(env.solver->einfo, 0, "UNKNOWN");
  }
}

void exit_OPT(const Env& env, const bigint& opt) {
  if (env.solver->read) checkResults(opt, env.solver->storedResult);
  if (exiting.test_and_set()) return;
  assert(env.solver->foundSolution());
  if (options.verbosity.get() > 0) stats.print();
  std::cout << "o " << opt << std::endl;
  std::cout << "s OPTIMUM FOUND" << std::endl;
  if (options.printSol) printSol(*env.solver, env.solver->lastSol);
  if (env.logger) env.logger->optimum(opt, env.solver->lastSol);
  if (env.solver->write) writeFinalStatus(env.solver->einfo, opt, "OPT");
}

void exit_UNSAT(const Env& env) {
  if (env.solver->read) checkResults(0, env.solver->storedResult);
  if (exiting.test_and_set()) return;
  assert(not env.solver->foundSolution());
  if (options.verbosity.get() > 0) stats.print();
  puts("s UNSATISFIABLE");
  if (env.logger) env.logger->unsat();
  if (env.solver->write) writeFinalStatus(env.solver->einfo, 0, "UNSAT");
}

void exit_INDETERMINATE(const Env& env) {
  if (env.solver->read) checkResults(0, env.solver->storedResult);
  if (exiting.test_and_set()) return;
  if (env.logger) env.logger->bailout();
  if (options.verbosity.get() > 0) stats.print();
  if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get())
    puts("s TIMELIMIT");
  else
    puts("s UNKNOWN");
  if (env.solver->write) writeFinalStatus(env.solver->einfo, 0, "UNKNOWN");
}

void exit_ERROR(const std::initializer_list<std::string>& messages) {
  if (exiting.test_and_set()) return;
  std::cout << "Error: ";
  for (const std::string& m : messages) std::cout << m;
  std::cout << std::endl;
  exit(1);
}

}  // namespace rs::quit

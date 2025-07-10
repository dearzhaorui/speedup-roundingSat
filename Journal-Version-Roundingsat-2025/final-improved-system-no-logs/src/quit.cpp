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

void exit_SAT(const Env& env) {
  if (exiting.test_and_set()) return;
  assert(env.solver->foundSolution());
  if (env.logger) {
    env.logger->solution(env.solver->lastSol);
    env.logger->sat(env.solver->lastSol);
  }
  if (options.verbosity.get() > 0) stats.print();
  puts("s SATISFIABLE");
  if (options.printSol) printSol(*env.solver, env.solver->lastSol);
}

void exit_INDETERMINATE(const Env& env, const bigint& lb, const bigint& ub) {
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
    puts("s SATISFIABLE");
    if (options.printSol) printSol(*env.solver, env.solver->lastSol);
  } else {
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get())
      puts("s TIMELIMIT");
    else
      puts("s UNKNOWN");
  }
}

void exit_OPT(const Env& env, const bigint& opt) {
  if (exiting.test_and_set()) return;
  assert(env.solver->foundSolution());
  if (options.verbosity.get() > 0) stats.print();
  std::cout << "o " << opt << std::endl;
  std::cout << "s OPTIMUM FOUND" << std::endl;
  if (options.printSol) printSol(*env.solver, env.solver->lastSol);
  if (env.logger) env.logger->optimum(opt, env.solver->lastSol);
}

void exit_UNSAT(const Env& env) {
  if (exiting.test_and_set()) return;
  assert(not env.solver->foundSolution());
  if (options.verbosity.get() > 0) stats.print();
  puts("s UNSATISFIABLE");
  if (env.logger) env.logger->unsat();
}

void exit_INDETERMINATE(const Env& env) {
  if (exiting.test_and_set()) return;
  if (env.logger) env.logger->bailout();
  if (options.verbosity.get() > 0) stats.print();
  if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get())
    puts("s TIMELIMIT");
  else
    puts("s UNKNOWN");
}

void exit_ERROR(const std::initializer_list<std::string>& messages) {
  if (exiting.test_and_set()) return;
  std::cout << "Error: ";
  for (const std::string& m : messages) std::cout << m;
  std::cout << std::endl;
  exit(1);
}

}  // namespace rs::quit

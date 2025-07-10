/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

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

#pragma once

#include "Constraint.hpp"
#include "Solver.hpp"
#include "typedefs.hpp"

namespace run {
std::vector<bool> solution;
intConstr aux;
intConstr core;
Val upper_bound;
Val lower_bound;
Solver solver;
intConstr objective;

inline void printObjBounds(Val lower, Val upper) {
  if (options.verbosity == 0) return;
  if (upper < std::numeric_limits<Val>::max())
    printf("c bounds %10lld >= %10lld\n", upper, lower);
  else
    printf("c bounds          - >= %10lld\n", lower);
}

void handleNewSolution(const intConstr& origObj, ID& lastUpperBound) {
  Val prev_val = upper_bound;
  _unused(prev_val);
  upper_bound = -origObj.getRhs();
  for (Var v : origObj.vars) upper_bound += origObj.coefs[v] * solution[v];
  assert(upper_bound < prev_val);
  solver.bestSoFar = upper_bound;
  
  origObj.copyTo(aux);
  aux.invert();
  aux.addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, (options.readFile? false:true));
  lastUpperBound = solver.addConstraint(aux, ConstraintType::EXTERNAL);
  aux.reset();
  
  std::cout << "c BestSoFar: " << upper_bound << ", nSolu= " << stats.NSOLS << std::endl;
  
  if (lastUpperBound == ID_Unsat) quit::exit_UNSAT(solution, upper_bound, solver.logger, solver.getStoredResult(), solver.einfo);
}

void optimize(intConstr& origObj) {
  assert(origObj.vars.size() > 0);
  // NOTE: -origObj.getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  origObj.removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
  lower_bound = -origObj.getDegree();
  upper_bound = std::numeric_limits<Val>::max();
  core.initializeLogging(solver.logger);

  Val opt_coef_sum = 0;
  for (Var v : origObj.vars) opt_coef_sum += std::abs(origObj.coefs[v]);
  //if (opt_coef_sum >= (Val)INF)
    //quit::exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});  // TODO: remove restriction

  longConstr reformObj;
  origObj.copyTo(reformObj);
  ID lastUpperBound = ID_Undef;
  
  if (options.readFile) {
    solver.initLogReader(options.exec);
    solver.logReader->readUntilNextCleanup();
  }
  else if (options.writeFile) {
    std::ofstream* einfo = new std::ofstream(options.exec);
    solver.setExecutionFileName(einfo);
  }

  size_t upper_time = 0;
  SolveState reply = SolveState::SAT;
  while (true) {
    size_t current_time = stats.getDetTime();
    //if (reply != SolveState::INPROCESSED && reply != SolveState::RESTARTED) printObjBounds(lower_bound, upper_bound);
    assert(upper_bound > lower_bound);
    reply = (solver.read? solver.solve_read({}, core, solution) : solver.solve({}, core, solution));
    
    if (reply == SolveState::INTERRUPTED) {
      std::cout << "\nINTERRUPTED: Solving is finished....\n" << std::flush;
      if (!solver.lemmas.empty() or !solver.allDecisions.empty()) {
        cout << "#lemmas " << solver.lemmas.size() << ", #decisions " << solver.allDecisions.size() << endl;
        exit(0);
      }
      quit::exit_INDETERMINATE(solution, upper_bound, solver.logger, solver.getStoredResult(), solver.einfo);
    }
    if (reply == SolveState::RESTARTED) continue;
    if (reply == SolveState::UNSAT) quit::exit_UNSAT(solution, upper_bound, solver.logger, solver.getStoredResult(), solver.einfo);
    assert(solver.decisionLevel() == 0);
    upper_time += stats.getDetTime() - current_time;
    
    if (reply == SolveState::SAT) {
      assert(solution.size() > 0);
      ++stats.NSOLS;
      handleNewSolution(origObj, lastUpperBound);
    } else if (reply == SolveState::INCONSISTENT) {
      assert(false);
      assert(core.getSlack(solver.getLevel()) < 0);
      if (solver.logger) core.logInconsistency(solver.getLevel(), solver.getPos(), stats);
      assert(solver.decisionLevel() == 0);
      quit::exit_UNSAT(solution, upper_bound, solver.logger, solver.getStoredResult(), solver.einfo);
    } else
      assert(reply == SolveState::INPROCESSED);  // keep looping
  }
}

void decide() {
  while (true) {
    SolveState reply = solver.solve({}, core, solution);
    assert(reply != SolveState::INCONSISTENT);
    if (reply == SolveState::INTERRUPTED) quit::exit_INDETERMINATE({}, 0, solver.logger, solver.getStoredResult(), solver.einfo);
    if (reply == SolveState::SAT)
      quit::exit_SAT(solution, 0, solver.logger, solver.getStoredResult(), solver.einfo);
    else if (reply == SolveState::UNSAT)
      quit::exit_UNSAT({}, 0, solver.logger, solver.getStoredResult(), solver.einfo);
  }
}

void run() {
  if (options.verbosity > 0)
    std::cout << "c #variables " << solver.getNbOrigVars() << " #constraints " << solver.getNbConstraints()
              << std::endl;
  if (objective.vars.size() > 0)
    optimize(objective);
  else
    decide();
}
}  // namespace run

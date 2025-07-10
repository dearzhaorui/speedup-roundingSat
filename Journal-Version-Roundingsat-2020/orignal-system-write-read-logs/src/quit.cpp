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

#include "quit.hpp"
#include <iostream>
#include "Logger.hpp"
#include "globals.hpp"


void writeFinalStatus(std::ofstream* out, const Val& bestObjVal, const std::string status) {
  if(!out->is_open()) {std::cout << "exec output file is not open!" << std::endl; return;}
  *out << "\nnumDecisions: " << stats.NDECIDE << "\n";
  *out << "numConflicts: " << stats.NCONFL << "\n";
  *out << "numOfSolutionsFound: " << stats.NSOLS << "\n";
  *out << "numOfRestarts: " << stats.NRESTARTS << "\n";
  *out << "numOfCleanUps: " << stats.NCLEANUP << "\n";
  *out << "costOfBestSolution: " << (status!="UNSAT"? (status!="UNKNOWN"? bestObjVal : 0) : 0) << "\n";
  *out << "finalStatus: " << status << "\n";
  
  delete out;
}

void quit::checkResults(Val bestObjVal, const Result& r) {
  if (!options.readFile) return;
  std::cout << "checkResults.... " << std::endl;
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
    std::cout << "numOfCleanups is not correct! Solver has " << stats.NCLEANUP << ", but the stored #Cleanups-1 is " << r.nCleanups-1 << std::endl; exit(0);}
  if(stats.NSOLS > 0 and bestObjVal != r.bestCost) {
    std::cout << "costOfBestSolution is not correct! Solver has " << bestObjVal << ", but the stored bestCost is " << r.bestCost << std::endl; exit(0);}
}

void quit::printSol(const std::vector<bool>& sol) {
  printf("v");
  for (Var v = 1; v < (Var)sol.size() - stats.NAUXVARS; ++v) printf(sol[v] ? " x%d" : " -x%d", v);
  printf("\n");
}

void quit::printSolAsOpb(const std::vector<bool>& sol) {
  for (Var v = 1; v < (Var)sol.size() - stats.NAUXVARS; ++v) {
    if (sol[v])
      std::cout << "+1 x" << v << " >= 1 ;\n";
    else
      std::cout << "-1 x" << v << " >= 0 ;\n";
  }
}

void quit::exit_SAT(const std::vector<bool>& sol, Val bestObjVal, const std::shared_ptr<Logger>& logger, const Result& r, std::ofstream* out) {
  if (logger) logger->flush();
  if (options.verbosity > 0) stats.print();
  if(options.writeFile) writeFinalStatus(out, bestObjVal, "SAT");
  checkResults(bestObjVal, r);
  std::cout << "Cost of best solution: " << bestObjVal << std::endl;
  puts("s SATISFIABLE Some_solution_found SAT");
  if (options.printSol) printSol(sol);
  exit(10);
}

void quit::exit_UNSAT(const std::vector<bool>& sol, Val bestObjVal, const std::shared_ptr<Logger>& logger, const Result& r, std::ofstream* out) {
  if (logger) logger->flush();
  if (options.verbosity > 0) stats.print();
  
  checkResults(bestObjVal, r);
  
  if (sol.size() > 0) {
    if(options.writeFile) writeFinalStatus(out, bestObjVal, "OPT");
    std::cout << "o " << bestObjVal << std::endl;
    std::cout << "Cost of best solution: " << bestObjVal << std::endl;
    std::cout << "s Optimum_found OPT s OPTIMUM FOUND" << std::endl;
    if (options.printSol) printSol(sol);
    exit(30);
  } else {
    //puts("s UNSATISFIABLE");
    if(options.writeFile) writeFinalStatus(out, bestObjVal, "UNSAT");
    puts("s UNSATISFIABLE Infeasible UNSAT");
    exit(20);
  }
}

void quit::exit_INDETERMINATE(const std::vector<bool>& sol, Val bestObjVal, const std::shared_ptr<Logger>& logger, const Result& r, std::ofstream* out) {
  if (sol.size() > 0) exit_SAT(sol, bestObjVal, logger, r, out);
  if (logger) logger->flush();
  if (options.verbosity > 0) stats.print();
  if(options.writeFile) writeFinalStatus(out, bestObjVal, "UNKNOWN");
  checkResults(bestObjVal, r);
  puts("s UNKNOWN No_solution_found");
  exit(0);
}

void quit::exit_ERROR(const std::initializer_list<std::string>& messages) {
  std::cout << "Error: ";
  for (const std::string& m : messages) std::cout << m;
  std::cout << std::endl;
  exit(1);
}

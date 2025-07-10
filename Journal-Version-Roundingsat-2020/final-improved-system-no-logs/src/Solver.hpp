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

#include <memory>
#include <climits>
#include "IntSet.hpp"
#include "Options.hpp"
#include "SolverStructs.hpp"
#include "typedefs.hpp"

#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <unistd.h>
#include <cinttypes>
#include <iomanip>

using namespace std;

class Logger;

enum SolveState { SAT, UNSAT, INCONSISTENT, INTERRUPTED, INPROCESSED, RESTARTED };
enum WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };

class Solver {
  // ---------------------------------------------------------------------
  // Members
 private:
  int n;
  int orig_n;
  ID crefID = ID_Trivial;
  uint32_t iID = 0; // internal_ID: used also for index the slack, equal to slackMM.size()

  ConstraintAllocator ca;
  IntSet tmpSet;
  IntSet actSet;
  intConstr tmpConstraint;
  longConstr conflConstraint;  // functions as old confl_data
  intConstr logConstraint;
  OrderHeap order_heap;

  std::vector<CRef> constraints;
  std::vector<Val>  slackMM;  // sumOfNonFalse - degree - maxCoef, slackMM.size() == iID 
  
  std::unordered_map<ID, CRef> external;
  std::vector<std::vector<Watch>> _adj = {{}};
  std::vector<std::vector<Watch>>::iterator adj;
  std::vector<int> _Level = {INF};
  IntVecIt Level;  // TODO: make Pos, Level, contiguous memory for better cache efficiency.
  std::vector<Lit> trail;
  std::vector<int> trail_lim, Pos;
  std::vector<CRef> Reason;
  int qhead = 0;  // for unit propagation
  std::vector<Lit> phase;
  std::vector<ActValV> activity;

  long long nconfl_to_reduce = 2000;
  long long nconfl_to_restart = 0;
  ActValV v_vsids_inc = 1.0;
  ActValC c_vsids_inc = 1.0;

  std::vector<SimpleConsInt> learnedStack;

 public:
  std::shared_ptr<Logger> logger;

  Solver();
  void init();  // call after having read options

  int getNbVars() const { return n; }
  void setNbVars(long long nvars);
  int getNbOrigVars() const { return orig_n; }
  void setNbOrigVars(int o_n);

  const IntVecIt& getLevel() const { return Level; }
  const std::vector<int>& getPos() const { return Pos; }
  int decisionLevel() const { return trail_lim.size(); }

  ID addConstraint(const intConstr& c, ConstraintType type);
  ID addConstraint(const SimpleConsInt& c, ConstraintType type);
  void dropExternal(ID id);
  int getNbConstraints() const { return constraints.size(); }
  void getIthConstraint(int i, intConstr& out) const { return ca[constraints[i]].toConstraint(out); }
  
  inline double totalTime() {return (aux::cpuTime()-stats.STARTTIME);}
  bool timeout() {
    if(options.tlimit and (totalTime() >= options.tlimit)) {
      std::cout << std::endl << std::endl << "Time limit exceeded. " << std::endl;
      return true;
    }
    return false;
  }
  
  double luby(double y, int i);

  
  /**
   * @return:
   *  UNSAT if root inconsistency detected
   *  SAT if satisfying assignment found
   *  INCONSISTENT if no solution extending assumptions exists
   *  INTERRUPTED if interrupted by external signal
   *  INPROCESSING if solver just finished a cleanup phase
   * @param assumptions: set of assumptions
   * @param core: if INCONSISTENT, implied constraint falsified by assumptions, otherwise untouched
   *  if core is the empty constraint, at least one assumption is falsified at root
   * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
   */
  SolveState solve(const IntSet& assumptions, intConstr& core, std::vector<bool>& solution);

 private:
  void presolve();
  
  // ---------------------------------------------------------------------
  // VSIDS

  void vDecayActivity();
  void vBumpActivity(Var v);
  void cDecayActivity();
  void cBumpActivity(Constr& c);

  // ---------------------------------------------------------------------
  // Trail manipulation

  void uncheckedEnqueue(Lit p, CRef from);
  void undoOne();
  void backjumpTo(int level);
  void decide(Lit l);
  void propagate(Lit l, CRef reason);
  /**
   * Unit propagation with watched literals.
   * @post: all constraints have been checked for propagation under trail[0..qhead[
   * @return: true if inconsistency is detected, false otherwise. The inconsistency is stored in conflConstraint.
   */
  bool runPropagation();
  WatchStatus checkForPropagation(Watch& watch, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  void recomputeLBD(Constr& C);
  bool analyze();
  bool extractCore(const IntSet& assumptions, intConstr& outCore, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  CRef attachConstraint(intConstr& constraint, ConstraintType type);
  template <typename S, typename L>
  void learnConstraint(Constraint<S, L>& c) {
    if (c.plogger)
      c.logProofLineWithInfo("Learn", stats);
    else
      c.id = ++crefID;
    learnedStack.push_back(c.template toSimpleCons<Coef, Val>());
  }
  CRef processLearnedStack();
  ID addInputConstraint(ConstraintType type);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect(const std::vector<int>& oldId2NewId);
  void reduceDB();
  // ---------------------------------------------------------------------
  // Solving

  //double luby(double y, int i);
  Val lhs(Constr& C, const std::vector<bool>& sol);
  bool checksol(const std::vector<bool>& sol);
  Lit pickBranchLit();
  
  public:
  uint64_t maximum_resident_set_size () {
    struct rusage u;
    if (getrusage (RUSAGE_SELF, &u)) return 0;
    //return ((uint64_t) u.ru_maxrss) << 10; // m/(double)(1l<<20)
    return (((uint64_t) u.ru_maxrss) << 10)/((double)(1l<<20)); // m/(double)(1l<<20)
  }
  
  uint64_t current_resident_set_size () {
    char path[40];
    sprintf (path, "/proc/%" PRId64 "/statm", (int64_t) getpid ());
    FILE * file = fopen (path, "r");
    if (!file) return 0;
    uint64_t dummy, rss;
    int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
    fclose (file);
    //return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
    return scanned == 2 ? (rss * sysconf (_SC_PAGESIZE))/((double)(1l<<20)) : 0;
  }
  
};

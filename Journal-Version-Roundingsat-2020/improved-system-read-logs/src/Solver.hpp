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
#include "IntSet.hpp"
#include "Options.hpp"
#include "SolverStructs.hpp"
#include "typedefs.hpp"
#include "ExecInfo.hpp"
#include "file.hpp"
#include <iostream>
#include <queue>
#include <fstream>
#include <string>
#include <algorithm>
#include <unordered_map>

using namespace std;

class Logger;
class File;

enum SolveState { SAT, UNSAT, INCONSISTENT, INTERRUPTED, INPROCESSED, RESTARTED };
enum WatchStatus { DROPWATCH, KEEPWATCH, CONFLICTING };

class Solver {
  friend class File;
  // ---------------------------------------------------------------------
  // Members
 private:
  int n;
  int orig_n;
  ID crefID = 0; // ID_Trivial;
  uint32_t iID = 0; // internalID used also for formula constraints, equal to slackMCoef.size()

  ConstraintAllocator ca;
  IntSet tmpSet;
  IntSet actSet;
  intConstr tmpConstraint;
  longConstr conflConstraint;  // functions as old confl_data
  intConstr logConstraint;
  OrderHeap order_heap;

  std::vector<CRef> constraints;
  std::vector<long long>  slackMCoef;//  = {CounterGarbageInfo()};  // slack - maxCoef, slackMCoef.size()-1 == iID 
  std::vector<uint32_t> id2iID = {0};  // used in cleanup for identifying which ctr should be deleted

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
  std::shared_ptr<File>   logReader;
  
  bool conflict = false;
  Result storedResult;
  CleanupInfo nextCleanupInfo;
  std::queue<int> allDecisions;  // stored decs
  std::queue<Lemma> lemmas;
 

  Solver();
  void init();  // call after having read options
  Val bestSoFar;
  int64_t memAfterReading;

  int getNbVars() const { return n; }
  void setNbVars(long long nvars);
  int getNbOrigVars() const { return orig_n; }
  void setNbOrigVars(int o_n);
  
  Result getStoredResult() const {return storedResult;}
  void initLogReader(std::string nameFile);

  const IntVecIt& getLevel() const { return Level; }
  const std::vector<int>& getPos() const { return Pos; }
  int decisionLevel() const { return trail_lim.size(); }

  ID addConstraint(const intConstr& c, ConstraintType type);
  ID addConstraint(const SimpleConsInt& c, ConstraintType type);
  void dropExternal(ID id, bool forceDelete);
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
  void readLemma();
  void readCores();

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
    //else
      //c.id = ++crefID;
    learnedStack.push_back(c.template toSimpleCons<Coef, Val>());
  }
  CRef processLearnedStack();
  CRef processLearnedStack_read();
  ID addInputConstraint(ConstraintType type);
  void removeConstraint(Constr& C);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect(std::vector<int>& oldId2NewId);
  void reduceDB();

  // ---------------------------------------------------------------------
  // Solving

  double luby(double y, int i);
  Val lhs(Constr& C, const std::vector<bool>& sol);
  bool checksol(const std::vector<bool>& sol);
  Lit pickBranchLit();
  
 public: // CADICAL code
  int64_t maximum_resident_set_size();
  int64_t current_resident_set_size();
};

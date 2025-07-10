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

#pragma once

#include <memory>
#include "Env.hpp"
#include "IntSet.hpp"
#include "SolverStructs.hpp"
#include "typedefs.hpp"

#include <queue>
#include <fstream>
#include "ExecInfo.hpp"
#include "file.hpp"

namespace rs {

struct Logger;
class File;
enum class WatchStatus;

enum class SolveState { SOLVING, SAT, UNSAT, INCONSISTENT, INPROCESSED, RESTARTED, INTERRUPTED };

struct SolveAnswer {
  SolveState state;
  std::vector<CeSuper> cores;
  std::vector<Lit>& solution;
};

class Solver {
  friend class LpSolver;
  friend struct Constr;
  friend struct Clause;
  friend struct Cardinality;
  template <typename CF, typename DG>
  friend struct Counting;
  template <typename CF, typename DG>
  friend struct Watched;
  template <typename CF, typename DG>
  friend struct CountingSafe;
  template <typename CF, typename DG>
  friend struct WatchedSafe;

  // ---------------------------------------------------------------------
  // Members

 public:
  std::vector<Lit> lastSol = {0};
  bool foundSolution() const { return lastSol.size() > 1; }
  std::vector<CeSuper> cores;

 private:
  Env& env;
  Logger* logger;
  ConstrExpPools& cePools;
  std::unique_ptr<LpSolver>& lpSolver;

  int n = 0;
  int orig_n = 0;
  ID crefID = ID_Invalid;

  ConstraintAllocator ca;
  IntSet tmpSet;
  IntSet actSet;  // Set of literals that need their activity bumped after conflict analysis.

  std::vector<CRef> constraints;
  std::unordered_map<ID, CRef> external;
  std::vector<std::vector<Watch>> _adj = {{}};
  std::vector<std::vector<Watch>>::iterator adj;
  std::vector<int> _Level = {INF};
  IntVecIt Level;  // TODO: make Pos, Level, contiguous memory for better cache efficiency.
  std::vector<Lit> trail;
  std::vector<int> trail_lim;
  std::vector<int> Pos;  // Position for assignment of literal on the trail.
  std::vector<CRef> Reason;
  int qhead = 0;  // for unit propagation

  std::vector<Lit> phase;
  std::vector<ActValV> activity;
  OrderHeap order_heap;

  long long nconfl_to_reduce = 2000;
  long long nconfl_to_restart = 0;
  long long nconfl_to_return = std::numeric_limits<long long>::max();
  ActValV v_vsids_inc = 1.0;
  ActValC c_vsids_inc = 1.0;

  bool firstRun = true;

  std::vector<std::unique_ptr<ConstrSimpleSuper>> learnedStack;

  IntSet assumptions;
  std::vector<int> assumptions_lim;

  SolveState handleConflict(CeSuper confl);
  SolveState makeDecision();
  
  SolveState readLemmas(CeSuper confl, const Ce32& input, std::vector<CeSuper>& result);
  SolveState readDecision(const Ce32& input, std::vector<CeSuper>& result);

 public:
  int nextConfForCoreLem = -1;
  Result storedResult;
  CleanupInfo nextCleanupInfo;
  std::queue<char> assumpRefs;  // flag specifying whether to update assumptions ('1': yes, '0': no). because this information also depends on the spent time
  std::queue<char> direct0s;  // flag specifying the next step to be done when no conflict is found (i.e., extract core, process new solution, etc)
  std::queue<int> confCoreLem;  // stored decs
  std::queue<int> allDecisions;  // stored decision literals
  std::queue<Lemma> lemmas;
  std::queue<CoreCe> coreCes;
  
  std::ofstream* einfo; // the log file for writing execution information
  std::shared_ptr<File> logReader;
  bool write = false, read = false;
  int64_t memAfterReading;
  

 public:
  Solver(Env& env);
  void initLP(const CeArb objective);

  int getNbVars() const { return n; }
  void setNbVars(long long nvars, bool orig = false);
  int getNbOrigVars() const { return orig_n; }

  const IntVecIt& getLevel() const { return Level; }
  const std::vector<int>& getPos() const { return Pos; }
  int decisionLevel() const { return trail_lim.size(); }

  // result: formula line id, processed id
  std::pair<ID, ID> addConstraint(const CeSuper c, Origin orig);
  std::pair<ID, ID> addTempConstraint(CeSuper c, Origin orig);  // discard c after calling
  std::pair<ID, ID> addConstraint(const ConstrSimpleSuper& c, Origin orig);

  void dropExternal(ID id, bool erasable, bool forceDelete);
  int getNbConstraints() const { return constraints.size(); }

  void setAssumptions(const IntSet& assumps);
  const IntSet& getAssumptions() { return assumptions; }
  void setConflictBudget(long long budget);

  /**
   * @return SolveAnswer.state:
   *  UNSAT if root inconsistency detected
   *  SAT if satisfying assignment found
   *  INCONSISTENT if no solution extending assumptions exists
   *  INPROCESSING if solver just finished a cleanup phase
   * @return SolveAnswer.cores:
   *    implied constraints C if INCONSISTENT
   *        if C is a tautology, negated assumptions at root level exist
   *        if C is not a tautology, it is falsified by the assumptions
   * @return SolveAnswer.solution:
   *    the satisfying assignment if SAT
   */
  // TODO: use a coroutine / yield instead of a SolveAnswer return value
  SolveAnswer solve();
  SolveAnswer solve_read();
  
  // ---------------------------------------------------------------------
  // NEW FUNCTIONS : PUBLIC
  void setWriteOrReadInfo(bool w, bool r) {write = w; read = r;}
  void setExecutionFileName(std::ofstream* of) {einfo = of;}
  void initLogReader(std::string nameFile);

 private:
  void presolve();
  
  void readLemma( const Ce32& input);  // read from queues
  void readCores( const Ce32& input, std::vector<CeSuper>& result);

  // ---------------------------------------------------------------------
  // VSIDS

  /**
   * @brief Decay VSIDS score for all variables.
   *
   */
  void vDecayActivity();

  /**
   * @brief Increment VSIDS score for variable `v`.
   *
   * @param v Variable.
   */
  void vBumpActivity(Var v);

  /**
   * @brief Decay VSIDS score for all constraints.
   *
   */
  void cDecayActivity();

  /**
   * @brief Increment VSIDS score for constraint `c`
   *
   * @param c Constraint.
   */
  void cBumpActivity(Constr& c);

  // ---------------------------------------------------------------------
  // Trail manipulation

  /**
   * @brief Add assignment to trail without checking.
   *
   * @param p Literal to add to the trail.
   * @param from Reason for the assignment.
   */
  void uncheckedEnqueue(Lit p, CRef from);
  void removeLastAssignment();
  void backjumpTo(int level);

  /**
   * @brief Add assignment to trail that was caused by a decision.
   *
   * @param l Literal that was decided.
   */
  void decide(Lit l);

  /**
   * @brief Add assignment to trail that was caused by a propagation.
   *
   * @param l Literal to be added to the trail.
   * @param reason Reason for the propagation.
   */
  void propagate(Lit l, CRef reason);

  /**
   * Unit propagation with watched literals.
   * @post: all constraints have been checked for propagation under trail[0..qhead[
   * @return: true if inconsistency is detected, false otherwise. The inconsistency is stored in confl->
   */
  CeSuper runPropagation(bool onlyUnitPropagation);

  /**
   * @brief Checks if the constraint `cr` propagates.
   *
   * @param cr Reference to constraint to check.
   * @param idx Index of watched literal in the constraint.
   * @param p The currently propagated literal.
   * @return WatchStatus
   */
  WatchStatus checkForPropagation(CRef cr, int& idx, Lit p);

  // ---------------------------------------------------------------------
  // Conflict analysis

  void recomputeLBD(Constr& C);
  CeSuper prepareConflictConstraint(CeSuper conflict);
  /**
   * @brief Get initial set of literals that need their activity bumped after conflict analysis.
   *
   * @param confl Conflict side constraint.
   */
  void assignActiveSet(CeSuper confl);
  Constr& getReasonConstraint(Lit l);
  void trackReasonConstraintStats(Constr& reasonC);
  void bumpLiteralActivity();
  CeSuper analyze(CeSuper confl);
  void extractCore(CeSuper confl, const IntSet& assumptions, Lit l_assump = 0);

  // ---------------------------------------------------------------------
  // Constraint management

  CRef attachConstraint(CeSuper constraint, bool locked);
  void learnConstraint(const CeSuper c, Origin orig);
  CeSuper processLearnedStack();
  std::pair<ID, ID> addInputConstraint(CeSuper ce);
  void removeConstraint(Constr& C, bool override = false);

  // ---------------------------------------------------------------------
  // Garbage collection

  void garbage_collect();
  void reduceDB();
  void reduceDB_read();

  // ---------------------------------------------------------------------
  // Solving

  double luby(double y, int i) const;
  bool checkSAT();
  Lit pickBranchLit(bool lastSolPhase);
  
 public: // CADICAL code
  int64_t maximum_resident_set_size();
  int64_t current_resident_set_size();
};

}  // namespace rs

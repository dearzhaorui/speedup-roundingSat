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

#include "Solver.hpp"

#include <cmath>

#include "Constr.hpp"
#include "ConstrExpPool.hpp"
#include "Logger.hpp"
#include "LpSolver.hpp"
#include "auxiliary.hpp"
#include "globals.hpp"

namespace rs {

// ---------------------------------------------------------------------
// Initialization

  Solver::Solver(Env& env) : env(env), logger(env.logger.get()), cePools(*env.cePools), lpSolver(env.lpSolver), order_heap(activity) {
  ca.capacity(1024 * 1024);  // 4MB
}

void Solver::setNbVars(long long nvars, bool orig) {
  assert(nvars > 0);
  assert(nvars < INF);
  if (nvars <= n) return;
  aux::resizeIntMap(_adj, adj, nvars, resize_factor, {});
  aux::resizeIntMap(_Level, Level, nvars, resize_factor, INF);
  Pos.resize(nvars + 1, INF);
  Reason.resize(nvars + 1, CRef_Undef);
  activity.resize(nvars + 1, 1 / actLimitV);
  phase.resize(nvars + 1);
  cePools.resize(nvars + 1);
  order_heap.resize(nvars + 1);
  for (Var v = n + 1; v <= nvars; ++v) phase[v] = -v, order_heap.insert(v);
  // if (lpSolver) lpSolver->setNbVariables(nvars + 1); // Currently, LP solver only reasons on formula constraints
  n = nvars;
  if (orig) {
    orig_n = n;
    stats.NORIGVARS = n;
    stats.NAUXVARS = 0;
  } else {
    stats.NAUXVARS = n - orig_n;
  }
}

void Solver::initLP([[maybe_unused]] const CeArb objective) {
#if WITHSOPLEX
  if (options.lpPivotRatio.get() == 0) return;
  bool pureCNF = objective->vars.size() == 0;
  for (CRef cr : constraints) {
    if (!pureCNF) break;
    pureCNF = (ca[cr].degree() == 1);
  }
  if (pureCNF) return;
  try {
    lpSolver = std::make_unique<LpSolver>(*this, objective);
  } catch (...) {
    if (options.verbosity.get() > 0) std::cout << "c LP initialization crashed" << std::endl;
  }
#else
  return;
#endif  // WITHSOPLEX
}

// ---------------------------------------------------------------------
// VSIDS

void Solver::vDecayActivity() { v_vsids_inc *= (1 / options.varDecay.get()); }
void Solver::vBumpActivity(Var v) {
  assert(v > 0);
  if ((activity[v] += v_vsids_inc) > actLimitV) {  // Rescale
    for (Var x = 1; x <= n; ++x) {
      activity[x] /= actLimitV;
      activity[x] /= actLimitV;
    }
    v_vsids_inc /= actLimitV;
    v_vsids_inc /= actLimitV;
  }
  // Update heap with respect to new activity:
  if (order_heap.inHeap(v)) order_heap.percolateUp(v);
}

void Solver::cDecayActivity() { c_vsids_inc *= (1 / options.clauseDecay.get()); }
void Solver::cBumpActivity(Constr& c) {
  c.act += c_vsids_inc;
  if (c.act > actLimitC) {  // Rescale:
    for (size_t i = 0; i < constraints.size(); i++) {
      ca[constraints[i]].act /= actLimitC;
      ca[constraints[i]].act /= actLimitC;
    }
    c_vsids_inc /= actLimitC;
    c_vsids_inc /= actLimitC;
  }
}

// ---------------------------------------------------------------------
// Assignment manipulation

void Solver::uncheckedEnqueue(Lit p, CRef from) {
  assert(!isTrue(Level, p));
  assert(!isFalse(Level, p));
  assert(isUnknown(Pos, p));
  Var v = toVar(p);
  Reason[v] = from;
  if (decisionLevel() == 0) {
    Reason[v] = CRef_Undef;  // no need to keep track of reasons for unit literals
    if (logger) {
      ProofBuffer proof;
      Constr& C = ca[from];
      if (C.size() == 1 && C.coef(0) == 1) {
          // no need to log a new constraint: C is already the unit itself
        assert(C.degree() == 1);
        logger->unitIDs.push_back(ca[from].id);
        logger->protect.insert(ca[from].id);
      } else {
        std::vector<Lit> unitLitsC = C.falsifiedUnits(Level);
        std::vector<ID> hints;
        for (Lit l: unitLitsC)
          hints.push_back(logger->unitIDs[Pos[toVar(l)]]);
        hints.push_back(ca[from].id);
        proof.logUnit(*logger, p, hints);
      }
      assert(logger->unitIDs.size() == trail.size() + 1);
    }
  }
  Level[p] = decisionLevel();
  Pos[v] = (int)trail.size();
  trail.push_back(p);
}

void Solver::increaseSlack(const Watch& w) {
  SlackMC& smc = slackMCoefV[w.iID];
  assert(!smc.removed);
  if (w.isCoef()) {
    long long coef = std::abs(w.coeffOfLit());
    if (smc.isVal) {  // type of slack is long long
      smc.slackMC += coef;
    }
    else {            // type of slack is int128 or bigint
      unsigned int ssize  = smc.valueSize();
      if (ssize == SIGN_PTR_128) {   // type of slack is int128
        int128& v = *((int128*)(smc.ptrVal())); v += coef;
      }
      else {                         // type of slack is bigint
        bigint& v = *((bigint*)(smc.ptrVal())); v += coef;
      }
    }
    return;
  }

  assert(!smc.isVal);
  [[maybe_unused]] unsigned int ssize  = smc.valueSize();
  long long sptr  = smc.ptrVal();
  unsigned int csize  = w.coefSize();
  long long cptr      = w.ptrVal();

  if (csize == SIGN_PTR_64) {  // coef is int64_t
    assert(ssize == SIGN_PTR_128);
    int64_t coef = *(reinterpret_cast<int64_t*>(cptr));
    int128& v = *((int128*)(sptr));
    v += aux::abs(coef);
  }
  else if (csize == SIGN_PTR_128) {  // coef is int128
    assert(ssize == SIGN_PTR_128);
    int128& coef = *(reinterpret_cast<int128*>(cptr));
    int128& v = *((int128*)(sptr));
    v += aux::abs(coef);
  }
  else {
    assert(csize == SIGN_PTR_BIGINT && ssize == SIGN_PTR_BIGINT);   // slack is bigint
    bigint& coef = *(reinterpret_cast<bigint*>(cptr));
    bigint& v    = *(reinterpret_cast<bigint*>(sptr));
    v += aux::abs(coef);
  }
}

void Solver::removeLastAssignment() {
  assert(!trail.empty());
  ++stats.NTRAILPOPS;
  Lit l = trail.back();
  if (qhead == (int)trail.size()) {
    for (const Watch& w : adj[-l]) {
      if (w.isPB()) increaseSlack(w);
    }
    --qhead;
  }
  Var v = toVar(l);
  trail.pop_back();
  Level[l] = INF;
  Pos[v] = INF;
  phase[v] = l;
  if (!trail_lim.empty() && trail_lim.back() == (int)trail.size()) trail_lim.pop_back();
  order_heap.insert(v);
}

void Solver::backjumpTo(int level) {
  assert(level >= 0);
  while (decisionLevel() > level) removeLastAssignment();
}

void Solver::decide(Lit l) {
  ++stats.NDECIDE;
  trail_lim.push_back(trail.size());
  uncheckedEnqueue(l, CRef_Undef);
}

void Solver::propagate(Lit l, CRef reason) {
  assert(reason != CRef_Undef);
  ++stats.NPROP;
  uncheckedEnqueue(l, reason);
}

/**
 * Unit propagation with watched literals.
 * @post: all watches up to trail[qhead] have been propagated
 */
 // original version
CeSuper Solver::runPropagation(bool onlyUnitPropagation) {
  CeSuper confl = processLearnedStack();
  if (confl) {
    return confl;
  }
  
  while (qhead < (int)trail.size()) {
    Lit p = trail[qhead++];
    std::vector<Watch>& ws = adj[-p];
    
    for (int it_ws = 0; it_ws < (int)ws.size(); ++it_ws) {
      int idx = ws[it_ws].idx;
      
      if (idx < 0 && isTrue(Level, idx + INF)) {
        assert(dynamic_cast<Clause*>(&(ca[constraints[ws[it_ws].iID]])) != nullptr);
        continue;
      }  // blocked literal check
      WatchStatus wstat = checkForPropagation(ws[it_ws], -p);
      
      if (wstat == WatchStatus::DROPWATCH) {
        swapErase_watches(ws, it_ws--);
      }
      else if (wstat == WatchStatus::CONFLICTING) {  // clean up current level and stop propagation
        ++stats.NTRAILPOPS;
        for (int i = 0; i <= it_ws; ++i) {
          if (ws[i].isPB()) increaseSlack(ws[i]);
        }
        --qhead;
  
        CRef cr = constraints[ws[it_ws].iID];
        Constr& C = ca[cr];
        if (!C.isLocked()) {
          cBumpActivity(C);
          recomputeLBD(C);
        }

        stats.NENCFORMULA += C.getOrigin() == Origin::FORMULA;
        stats.NENCLEARNED += C.getOrigin() == Origin::LEARNED;
        stats.NENCBOUND += (C.getOrigin() == Origin::LOWERBOUND || C.getOrigin() == Origin::UPPERBOUND ||
                            C.getOrigin() == Origin::HARDENEDBOUND);
        stats.NENCCOREGUIDED += C.getOrigin() == Origin::COREGUIDED;
        stats.NLPENCGOMORY += C.getOrigin() == Origin::GOMORY;
        stats.NLPENCLEARNEDFARKAS += C.getOrigin() == Origin::LEARNEDFARKAS;
        stats.NLPENCFARKAS += C.getOrigin() == Origin::FARKAS;

        return C.toExpanded(cePools);
      }
    }
  }
  if (onlyUnitPropagation) return CeNull();
  if (lpSolver) {
    try {
      std::pair<LpStatus, CeSuper> lpResult =
          aux::timeCall<std::pair<LpStatus, CeSuper>>([&] { return lpSolver->checkFeasibility(); }, stats.LPTOTALTIME);
      assert((lpResult.first == LpStatus::INFEASIBLE) == (lpResult.second && lpResult.second->hasNegativeSlack(Level)));
      return lpResult.second;
    } catch (...) {
      lpSolver.reset();
      if (options.verbosity.get() > 0) std::cout << "c Disabling crashed LP" << std::endl;
    }
  }
  return CeNull();
  ;
}

 /**
 * Lazily unwatch the falsified literal for watched PBs 
 * unless it's really necessary to load the constraint for more watches.
 * It works as counting propagation, which would reduce the number of constraint loads.
 */
WatchStatus Solver::checkForPropagation(Watch& watch, Lit p) {
  const int32_t iID = watch.iID; 
  if (slackMCoefV[iID].removed) return WatchStatus::DROPWATCH;
  
  assert(isFalse(Level, p));
  ++stats.NWATCHLOOKUPS;
  
  if (watch.isPB()) {
    ++stats.NPBWATCHES;
    SlackMC& smc = slackMCoefV[iID];
  
    bool checkForProp = false;
    if (watch.isCoef()) { // the coef value
      long long coef = std::abs(watch.coeffOfLit());
      if (smc.isVal) { smc.slackMC -= coef; checkForProp = (smc.slackMC < 0);}
      else {  // slack is large
        unsigned int ssize = smc.valueSize();
        long long    sptr  = smc.ptrVal();
        if (ssize == SIGN_PTR_128) { int128& v = *((int128*)sptr); v -= coef; checkForProp = (v < 0);}
        else                       { bigint& v = *((bigint*)sptr); v -= coef; checkForProp = (v < 0);}
      }
    }
    else {  // slack and coef are saved as pointers
      assert(!smc.isVal);
      [[maybe_unused]] unsigned int ssize  = smc.valueSize();  
      long long sptr = smc.ptrVal();
      unsigned int csize  = watch.coefSize(); 
      long long cptr = watch.ptrVal();
  
      if (csize == SIGN_PTR_64) {  // coef is int64_t
        assert(ssize == SIGN_PTR_128);
        int64_t coef = *(reinterpret_cast<int64_t*>(cptr));
        int128& v = *((int128*)sptr); v -= aux::abs(coef); checkForProp = (v < 0);
      } 
      else if (csize == SIGN_PTR_128) {  // coef is int128
        assert(ssize == SIGN_PTR_128);
        int128& coef = *(reinterpret_cast<int128*>(cptr));
        int128& v = *((int128*)sptr); v -= aux::abs(coef); checkForProp = (v < 0);
      }
      else {                                
        assert(csize == SIGN_PTR_BIGINT && ssize == SIGN_PTR_BIGINT); 
        bigint& coef = *(reinterpret_cast<bigint*>(cptr)); 
        bigint& v    = *(reinterpret_cast<bigint*>(sptr));
        v -= aux::abs(coef); checkForProp = (v < 0);
      }
    }
    
    if (checkForProp) {CRef cr = constraints[iID]; return ca[cr].checkForPropagation(cr, watch.idx, p, *this, iID);}
    else return WatchStatus::KEEPWATCH;
  }
  
  // clause or cardinalities
  assert(watch.isSimple()); 
  CRef cr = constraints[iID];
  return ca[cr].checkForPropagation(cr, watch.idx, p, *this, iID);
}

// ---------------------------------------------------------------------
// Conflict analysis

void Solver::recomputeLBD(Constr& C) {
  if (C.lbd() > 2) {  // constraints with LBD <= 2 won't have score recomputed
    assert(tmpSet.isEmpty());
    for (int i = 0; i < (int)C.size(); i++)
      if (isFalse(Level, C.lit(i))) tmpSet.add(Level[-C.lit(i)]);
    if (C.lbd() > tmpSet.size() + 1) C.setLBD(tmpSet.size());  // simulate Glucose
    tmpSet.clear();
  }
}

CeSuper getAnalysisCE(const CeSuper& conflict, int bitsOverflow, ConstrExpPools& cePools) {
  if (bitsOverflow == 0 || bitsOverflow > conflLimit128) {
    CeArb confl = cePools.takeArb();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit96) {
    Ce128 confl = cePools.take128();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit64) {
    Ce96 confl = cePools.take96();
    conflict->copyTo(confl);
    return confl;
  } else if (options.bitsOverflow.get() > conflLimit32) {
    Ce64 confl = cePools.take64();
    conflict->copyTo(confl);
    return confl;
  } else {
    Ce32 confl = cePools.take32();
    conflict->copyTo(confl);
    return confl;
  }
}

CeSuper Solver::prepareConflictConstraint(CeSuper conflict) {
  conflict->removeUnitsAndZeroes(Level, Pos);
  conflict->saturateAndFixOverflow(getLevel(), (bool)options.weakenFull, options.bitsOverflow.get(),
                                   options.bitsReduced.get(), 0);
  CeSuper confl = getAnalysisCE(conflict, options.bitsOverflow.get(), cePools);
  conflict->reset();
  return confl;
}

void Solver::assignActiveSet(CeSuper confl) {
  assert(actSet.isEmpty());  // will hold the literals that need their activity bumped
  for (Var v : confl->vars) {
    if (options.bumpLits)
      actSet.add(confl->getLit(v));
    else if (!options.bumpOnlyFalse || isFalse(Level, confl->getLit(v)))
      actSet.add(v);
  }
}

Constr& Solver::getReasonConstraint(Lit l) {
  assert(isPropagated(Reason, l));
  Constr& reasonC = ca[Reason[toVar(l)]];
  if (!reasonC.isLocked()) {
    cBumpActivity(reasonC);
    recomputeLBD(reasonC);
  }

  trackReasonConstraintStats(reasonC);

  return reasonC;
}

void Solver::trackReasonConstraintStats(Constr& reasonC) {
  stats.NENCFORMULA += reasonC.getOrigin() == Origin::FORMULA;
  stats.NENCLEARNED += reasonC.getOrigin() == Origin::LEARNED;
  stats.NENCBOUND += (reasonC.getOrigin() == Origin::LOWERBOUND || reasonC.getOrigin() == Origin::UPPERBOUND ||
                      reasonC.getOrigin() == Origin::HARDENEDBOUND);
  stats.NENCCOREGUIDED += reasonC.getOrigin() == Origin::COREGUIDED;
  stats.NLPENCGOMORY += reasonC.getOrigin() == Origin::GOMORY;
  stats.NLPENCLEARNEDFARKAS += reasonC.getOrigin() == Origin::LEARNEDFARKAS;
  stats.NLPENCFARKAS += reasonC.getOrigin() == Origin::FARKAS;
  ++stats.NRESOLVESTEPS;
}

void Solver::bumpLiteralActivity() {
  for (Lit l : actSet.getKeys())
    if (l != 0) vBumpActivity(toVar(l));
  actSet.clear();
}

CeSuper Solver::analyze(CeSuper conflict) {
  assert(conflict->hasNegativeSlack(Level));

  if (logger) logger->logComment("Analyze", stats);
  stats.NADDEDLITERALS += conflict->vars.size();

  CeSuper confl = prepareConflictConstraint(conflict);
  assignActiveSet(confl);

  while (decisionLevel() > 0) {
    if (asynch_interrupt) throw asynchInterrupt;
    Lit l = trail.back();
    if (confl->hasLit(-l)) {
      assert(confl->hasNegativeSlack(Level));

      AssertionStatus status = confl->isAssertingBefore(Level, decisionLevel());
      // Conflict constraint could now be asserting after removing some assignments.
      if (status == AssertionStatus::ASSERTING) break;
      // Constraint is already falsified by before last decision on trail.
      else if (status == AssertionStatus::FALSIFIED) {
        backjumpTo(decisionLevel() - 1);
        continue;
      }

      Constr& reasonC = getReasonConstraint(l);
      reasonC.resolveWith(confl, l, &actSet, *this);
    }
    removeLastAssignment();
  }
  bumpLiteralActivity();

  assert(confl->hasNegativeSlack(Level));
  return confl;
}

void Solver::extractCore(CeSuper conflict, const IntSet& assumptions, Lit l_assump) {
  if (l_assump != 0) {  // l_assump is an assumption propagated to the opposite value
    assert(assumptions.has(l_assump));
    assert(isFalse(Level, l_assump));
    int pos = Pos[toVar(l_assump)];
    while ((int)trail.size() > pos) removeLastAssignment();
    assert(isUnknown(Pos, l_assump));
    decide(l_assump);
  }

  // Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
  // For this, we first copy the trail, then backjump to 0, then rebuild the trail.
  // Otherwise, reordering the trail messes up the slacks of the watched constraints (see removeLastAssignment()).
  std::vector<Lit> decisions;  // holds the decisions
  decisions.reserve(decisionLevel());
  std::vector<Lit> props;  // holds the propagations
  props.reserve(trail.size());
  assert(trail_lim.size() > 0);
  for (int i = trail_lim[0]; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (assumptions.has(l) && (isDecided(Reason, l) || !options.cgResolveProp)) {
      decisions.push_back(l);
    } else {
      props.push_back(l);
    }
  }
  backjumpTo(0);

  for (Lit l : decisions) decide(l);                   // TODO: rename to recordDecision
  for (Lit l : props) propagate(l, Reason[toVar(l)]);  // TODO: rename to recodePropagation

  assert(conflict->hasNegativeSlack(Level));
  stats.NADDEDLITERALS += conflict->vars.size();
  conflict->removeUnitsAndZeroes(Level, Pos);
  conflict->saturateAndFixOverflow(getLevel(), (bool)options.weakenFull, options.bitsOverflow.get(),
                                   options.bitsReduced.get(), 0);
  assert(conflict->hasNegativeSlack(Level));
  CeSuper core = getAnalysisCE(conflict, options.bitsOverflow.get(), cePools);
  conflict->reset();

  int resolvesteps = l_assump == 0;  // if l==0, we already had some resolve steps in conflict analysis
  // analyze conflict
  if (core->hasNegativeSlack(assumptions)) {  // early termination core
    cores.push_back(core->clone(cePools));
    if (resolvesteps > 0) learnConstraint(cores.back(), Origin::LEARNED);
    resolvesteps = 0;
  }
  while (decisionLevel() > 0) {
    if (asynch_interrupt) throw asynchInterrupt;
    if (!options.cgDecisionCore && cores.size() > 0) break;
    Lit l = trail.back();
    if (core->hasLit(-l)) {
      if (isDecided(Reason, l)) break;  // no more propagated literals
      Constr& reasonC = ca[Reason[toVar(l)]];
      // TODO: stats? activity?
      reasonC.resolveWith(core, l, nullptr, *this);
      ++resolvesteps;
      if (cores.size() == 0 && core->hasNegativeSlack(assumptions)) {  // early termination core
        cores.push_back(core->clone(cePools));
        if (resolvesteps > 0) learnConstraint(cores.back(), Origin::LEARNED);
        resolvesteps = 0;
      }
    }
    removeLastAssignment();
  }
  if (options.cgDecisionCore && resolvesteps > 0) {  // decision core
    cores.push_back(core->clone(cePools));
    learnConstraint(cores.back(), Origin::LEARNED);  // TODO: These cores need to be tagged for IHS.
  }

  // weaken non-falsifieds
  for (CeSuper& cnfl : cores) {
    assert(cnfl->hasNegativeSlack(assumptions));
    assert(!cnfl->isTautology());
    assert(cnfl->isSaturated());
    for (Var v : cnfl->vars)
      if (!assumptions.has(-cnfl->getLit(v))) cnfl->weaken(v);
    cnfl->postProcess(Level, Pos, true, stats);
    assert(cnfl->hasNegativeSlack(assumptions));
  }
  backjumpTo(0);
}

// ---------------------------------------------------------------------
// Constraint management

CRef Solver::attachConstraint(CeSuper constraint, bool locked) {
  assert(constraint->isSortedInDecreasingCoefOrder());
  assert(constraint->isSaturated());
  assert(constraint->hasNoZeroes());
  assert(constraint->hasNoUnits(getLevel()));
  assert(!constraint->isTautology());
  assert(constraint->vars.size() > 0);
  assert(!constraint->hasNegativeSlack(getLevel()));
  assert(constraint->orig != Origin::UNKNOWN);

  ID id;
  if (logger) {
    id = constraint->logProofLineWithInfo("Attach", stats);
    logger->addRef(id);
  } else
    id = ++crefID;
  CRef cr = constraint->toConstr(ca, locked, id);
  Constr& C = ca[cr];
  C.initializeWatches(cr, *this);
  constraints.push_back(cr);
  ++iID;
  assert(slackMCoefV.size() == constraints.size());
  assert(slackMCoefV.size() == (size_t)iID);


  bool learned = (C.getOrigin() == Origin::LEARNED || C.getOrigin() == Origin::LEARNEDFARKAS ||
                  C.getOrigin() == Origin::FARKAS || C.getOrigin() == Origin::GOMORY);
  if (learned) {
    stats.LEARNEDLENGTHSUM += C.size();
    stats.LEARNEDDEGREESUM += C.degree();
  } else {
    stats.EXTERNLENGTHSUM += C.size();
    stats.EXTERNDEGREESUM += C.degree();
  }
  if (C.degree() == 1) {
    stats.NCLAUSESLEARNED += learned;
    stats.NCLAUSESEXTERN += !learned;
    if(learned) stats.CLAUSESLENGTHSUM    += C.size();
    else        stats.CLAUSESLENGTHSUMINI += C.size();
  } else if (C.largestCoef() == 1) {
    stats.NCARDINALITIESLEARNED += learned;
    stats.NCARDINALITIESEXTERN += !learned;
    if(learned) stats.CARDSLENGTHSUM    += C.size();
    else        stats.CARDSLENGTHSUMINI += C.size();
  } else {
    stats.NGENERALSLEARNED += learned;
    stats.NGENERALSEXTERN += !learned;
    if(learned) stats.PBSLENGTHSUM    += C.size();
    else        stats.PBSLENGTHSUMINI += C.size();
  }

  stats.NCONSFORMULA += C.getOrigin() == Origin::FORMULA;
  stats.NCONSLEARNED += C.getOrigin() == Origin::LEARNED;
  stats.NCONSBOUND += (C.getOrigin() == Origin::LOWERBOUND || C.getOrigin() == Origin::UPPERBOUND ||
                       C.getOrigin() == Origin::HARDENEDBOUND);
  stats.NCONSCOREGUIDED += C.getOrigin() == Origin::COREGUIDED;
  stats.NLPGOMORYCUTS += C.getOrigin() == Origin::GOMORY;
  stats.NLPLEARNEDFARKAS += C.getOrigin() == Origin::LEARNEDFARKAS;
  stats.NLPFARKAS += C.getOrigin() == Origin::FARKAS;

  return cr;
}

void Solver::learnConstraint(const CeSuper c, Origin orig) {
  assert(orig == Origin::LEARNED || orig == Origin::FARKAS || orig == Origin::LEARNEDFARKAS || orig == Origin::GOMORY);
  CeSuper learned = c->clone(cePools);
  learned->orig = orig;
  learned->saturateAndFixOverflow(getLevel(), (bool)options.weakenFull, options.bitsLearned.get(),
                                  options.bitsLearned.get(), 0);
  learnedStack.push_back(learned->toSimple());
}

// NOTE: backjumps to place where the constraint is not conflicting, as otherwise we might miss propagations
CeSuper Solver::processLearnedStack() {
  // loop back to front as the last constraint in the queue is a result of conflict analysis
  // and we want to first check this constraint to backjump.
  while (learnedStack.size() > 0) {
    CeSuper learned = learnedStack.back()->toExpanded(cePools);
    learnedStack.pop_back();
    learned->removeUnitsAndZeroes(Level, Pos);
    learned->sortInDecreasingCoefOrder();
    int assertionLevel = learned->getAssertionLevel(Level, Pos);
    if (assertionLevel < 0) {
      backjumpTo(0);
      return learned;
    }
    backjumpTo(assertionLevel);
    assert(!learned->hasNegativeSlack(Level));
    learned->heuristicWeakening(Level, Pos, stats);  // TODO: don't always weaken heuristically?
    learned->postProcess(Level, Pos, false, stats);
    assert(learned->isSaturated());
    if (learned->isTautology()) {
      continue;
    }
    CRef cr = attachConstraint(learned, false);
    Constr& C = ca[cr];
    if (assertionLevel < INF)  // check if is asserting
      recomputeLBD(C);
    else
      C.setLBD(C.size());  // the LBD of non-asserting constraints is undefined, so we take a safe upper bound
  }
  return CeNull();
}

std::pair<ID, ID> Solver::addInputConstraint(CeSuper ce) {
  assert(ce->orig == Origin::FORMULA || ce->orig == Origin::UPPERBOUND || ce->orig == Origin::LOWERBOUND ||
         ce->orig == Origin::HARDENEDBOUND || ce->orig == Origin::COREGUIDED);
  assert(decisionLevel() == 0);
  ID input = ID_Undef;
  if (logger) {
    if (ce->orig == Origin::FORMULA) {
      input = ce->logInput();
    } else if (ce->orig == Origin::UPPERBOUND) {
      input = logger->solution(lastSol);
      ce->logAssertEquals(input);
      ce->resetProof(input);
    } else if (ce->orig == Origin::LOWERBOUND) {
      input = ce->logProofLine();
    } else if (ce->orig == Origin::HARDENEDBOUND) {
      input = ce->logProofLine();
    } else if (ce->orig == Origin::COREGUIDED) {
      input = ce->logCG();
    } else {
      input = ce->logAsAssumption();
    }
  }
  ce->postProcess(Level, Pos, true, stats);
  if (ce->isTautology()) {
    return {input, ID_Undef};  // already satisfied.
  }

  if (ce->hasNegativeSlack(Level)) {
    if (options.verbosity.get() > 0) {
      if (ce->orig == Origin::FORMULA) puts("c Inconsistent input constraint");
      else if (ce->orig == Origin::HARDENEDBOUND) puts("c Inconsistent hardening constraint");
      else if (ce->orig == Origin::UPPERBOUND) puts("c Inconsistent objective-improving constraint");
      else puts("c Inconsistent constraint found");
    }
    if (logger) ce->logInconsistency(Level, Pos, stats);
    assert(decisionLevel() == 0);
    return {input, ID_Unsat};
  }

  if (options.bitsInput.get() != 0 && !ce->largestCoefFitsIn(options.bitsInput.get())) {
    ce->toStreamAsOPB(std::cerr);
    std::cerr << std::endl;
    quit::exit_ERROR({"Input constraint coefficient exceeds bit limit."});
  }

  CRef cr = attachConstraint(ce, true);
  
  ID id = ca[cr].id;
  Origin orig = ca[cr].getOrigin();
  if (orig != Origin::FORMULA) {
    external[id] = cr;
  }
  if (orig == Origin::LOWERBOUND || orig == Origin::UPPERBOUND) {
    lowerUpperBoundCtrIID[id] = iID-1; // for marking this objective ctr as deleted in dropExternal()
    assert(ce->orig == orig);
  }
  CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(true); }, stats.PROPTIME);
  if (confl) {
    assert(confl->hasNegativeSlack(Level));
    if (options.verbosity.get() > 0) {
      if (ce->orig == Origin::FORMULA) puts("c Input conflict");
      else if (ce->orig == Origin::HARDENEDBOUND) puts("c Conflict after adding hardening constraint");
      else if (ce->orig == Origin::UPPERBOUND) puts("c Conflict after adding objective-improving constraint");
      else puts("c Conflict after adding new constraint");
        // TODO: can we ever reach this point with a different Origin?
    }
    if (logger) confl->logInconsistency(Level, Pos, stats);
    assert(decisionLevel() == 0);
    return {input, ID_Unsat};
  }
  if (lpSolver && (orig == Origin::FORMULA || orig == Origin::UPPERBOUND || orig == Origin::LOWERBOUND)) {
    try {
      lpSolver->addConstraint(cr, false, orig == Origin::UPPERBOUND, orig == Origin::LOWERBOUND);
    } catch (...) {
      lpSolver.reset();
      if (options.verbosity.get() > 0) std::cout << "c Disabling crashed LP" << std::endl;
    }
  }
  return {input, id};
}

std::pair<ID, ID> Solver::addConstraint(const CeSuper c, Origin orig) {
  // NOTE: copy to temporary constraint guarantees original constraint is not changed and does not need logger
  CeSuper ce = c->clone(cePools);
  ce->orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  return result;
}

std::pair<ID, ID> Solver::addTempConstraint(CeSuper c, Origin orig) {
  // NOTE: do not use c after calling
  c->orig = orig;
  return addInputConstraint(c);
}

std::pair<ID, ID> Solver::addConstraint(const ConstrSimpleSuper& c, Origin orig) {
  CeSuper ce = c.toExpanded(cePools);
  ce->orig = orig;
  std::pair<ID, ID> result = addInputConstraint(ce);
  return result;
}

// called in reduceDB() for the proof information
void Solver::removeConstraintWithIID(int iID, [[maybe_unused]] bool override) {
  Constr& C = ca[constraints[iID]];
  assert(override || !C.isLocked());
  assert(!external.count(C.id));
  assert(!slackMCoefV[iID].removed);
  slackMCoefV[iID].removed = 1;

  // Delete proof log reference to a deleted constraint unless it is a unit.
  assert(C.size() > 1 || !logger || C.id == logger->unitIDs[Pos[toVar(C.lit(0))]]);
  if (logger && C.size() > 1) {
    logger->delRef(C.id);
  }
}

void Solver::removeConstraint(Constr& C, [[maybe_unused]] bool override) {
  assert(override || !C.isLocked());
  assert(!external.count(C.id));
  assert(C.getOrigin() == Origin::LOWERBOUND or C.getOrigin() == Origin::UPPERBOUND);
  auto old_it = lowerUpperBoundCtrIID.find(C.id);
  assert(old_it != lowerUpperBoundCtrIID.end());
  int iID = old_it->second;
  assert(iID >= 0 && iID < (int)slackMCoefV.size());
  lowerUpperBoundCtrIID.erase(old_it);
  assert(!slackMCoefV[iID].removed);
  slackMCoefV[iID].removed = 1;
  
  // Delete proof log reference to a deleted constraint unless it is a unit.
  assert(C.size() > 1 || !logger || C.id == logger->unitIDs[Pos[toVar(C.lit(0))]]);
  if (logger && C.size() > 1) {
    logger->delRef(C.id);
  }
}

void Solver::dropExternal(ID id, bool erasable, bool forceDelete) {
  assert(erasable || !forceDelete);
  if (id == ID_Undef) return;
  auto old_it = external.find(id);
  assert(old_it != external.end());
  Constr& constr = ca[old_it->second];
  external.erase(old_it);
  constr.setLocked(!erasable);
  if (forceDelete) removeConstraint(constr);
}

// ---------------------------------------------------------------------
// Assumptions

void Solver::setAssumptions(const IntSet& assumps) {
  assumptions = assumps;
  backjumpTo(0);
}

// ---------------------------------------------------------------------
// Garbage collection

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are deleted.
void Solver::garbage_collect() {
  ++stats.NGC;
  if (options.verbosity.get() > 0) puts("c GARBAGE COLLECT");

  ca.wasted = 0;
  ca.at = 0;
  std::unordered_map<uint32_t, CRef> crefmap;
  for (int i = 1; i < (int)constraints.size(); ++i) assert(constraints[i - 1].ofs < constraints[i].ofs);
  for (CRef& cr : constraints) {
    uint32_t offset = cr.ofs;
    size_t memSize = ca[cr].getMemSize();
    memmove(ca.memory + ca.at, ca.memory + cr.ofs, sizeof(uint32_t) * memSize);
    cr.ofs = ca.at;
    ca.at += memSize;
    crefmap[offset] = cr;
  }
#define update_ptr(cr) cr = crefmap[cr.ofs];
  for (Var v = 1; v <= n; ++v) {
    if (Reason[v] != CRef_Undef) update_ptr(Reason[v]);
  }
  for (auto& ext : external) update_ptr(ext.second);
#undef update_ptr
}

inline void Solver::swapErase_watches(std::vector<Watch>& indexable, size_t index) {
  indexable[index] = std::move(indexable.back());
  indexable.pop_back();
}

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are removed from memory.

void Solver::reduceDB() {
  assert(slackMCoefV.size() == constraints.size());
  assert((int)slackMCoefV.size() == iID);
  std::vector<std::pair<CRef, int>> learnts;
  learnts.reserve(constraints.size() / 2);

  int k = -1; 
  size_t totalLearnts = 0;
  size_t promisingLearnts = 0;
  for (CRef& cr : constraints) {
    ++k;
    Constr& C = ca[cr];
    if (slackMCoefV[k].removed || external.contains(C.id)) continue;
    bool isReason = false;
    for (unsigned int i = 0; i < C.size() && !isReason; ++i) {
      isReason = Reason[toVar(C.lit(i))] == cr;
    }
    if (isReason) continue;
    if (C.isSatisfiedAtRoot(Level))
      removeConstraintWithIID(k, true);
    else if (!options.keepAll && !C.isLocked()) {
      if (C.size() > 2 && C.lbd() > 2) learnts.emplace_back(cr, k);  // Keep all binary clauses and short LBDs
      if (C.size() <= 2 || C.lbd() <= 3) ++promisingLearnts;
      ++totalLearnts;
    }
  }

  if (promisingLearnts > totalLearnts / 2)
    nconfl_to_reduce += 10 * options.dbCleanInc.get();
  else
    nconfl_to_reduce += options.dbCleanInc.get();
  std::sort(learnts.begin(), learnts.end(), [&](auto& x, auto& y) {
    return ca[x.first].lbd() > ca[y.first].lbd() || (ca[x.first].lbd() == ca[y.first].lbd() && ca[x.first].act < ca[y.first].act);
  });
  for (size_t i = 0; i < std::min(totalLearnts / 2, learnts.size()); ++i) removeConstraintWithIID(learnts[i].second);
  
  std::vector<int> oldId2NewId(iID, -1);
  iID = 0;
  for (size_t k = 0; k < constraints.size(); ++k) {
    if (!slackMCoefV[k].removed) {
      oldId2NewId[k] = iID++;
    }
  }
  
#define update_iID(iid) iid = oldId2NewId[iid];
  for (auto& p : lowerUpperBoundCtrIID) { assert(p.second >= 0); update_iID(p.second); }
#undef update_iID

  std::vector<ID> logDeletions;
  size_t i = 0;
  size_t j = 0;
  for (; i < constraints.size(); ++i) {
    if (slackMCoefV[i].removed) {
      slackMCoefV[i].clear(); // explicitly destory the ptr 
      assert(oldId2NewId[i] == -1);
      Constr& c = ca[constraints[i]];
      ca.wasted += c.getMemSize();
      if (logger and c.getOrigin() == Origin::LEARNED and c.size() > 1) {
        logger->delRef(c.id);
      }
      c.freeUp();  // free up indirectly owned memory before implicitly deleting c during garbage collect
    } else {
      assert(oldId2NewId[i] > -1);
      constraints[j] = constraints[i]; 
      BigVal orig = slackMCoefV[i].slkMC();
      slackMCoefV[j++] = std::move(slackMCoefV[i]);
      assert(orig == slackMCoefV[j-1].slkMC());
      assert(i == j-1 or slackMCoefV[i].isVal);
    }
  }
  if (logger) logger->gc();
  assert((int)j == iID);
  for(; j < i; ++j) assert(slackMCoefV[j].isVal);
  constraints.resize(iID);
  slackMCoefV.resize(iID);
  if ((double)ca.wasted / (double)ca.at > 0.2) garbage_collect();
  
  // rebuild watch lists
  for (Lit l = -n; l <= n; ++l) {
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (oldId2NewId[adj[l][i].iID] == -1) {swapErase_watches(adj[l], i--);} 
      else {
        adj[l][i].iID = oldId2NewId[adj[l][i].iID];
        assert(adj[l][i].iID > -1);
        Watch& w = adj[l][i];
        if (!w.isCoef()) { // the pointer to the bigint coef will change after garbage collection
          assert(w.isPB());
          Constr& C = ca[constraints[w.iID]];
          long long cptr = C.getNewCoefPtr(w.idx-INF);
          assert(cptr != 0);
          w.setPtr(cptr);
        }
        
      }
    }
  }  
}



// ---------------------------------------------------------------------
// Solving

double Solver::luby(double y, int i) const {
  // Find the finite subsequence that contains index 'i', and the
  // size of that subsequence:
  int size, seq;
  for (size = 1, seq = 0; size < i + 1; seq++, size = 2 * size + 1) {
  }
  while (size != i + 1) {
    size = (size - 1) >> 1;
    --seq;
    assert(size != 0);
    i = i % size;
  }
  return std::pow(y, seq);
}

bool Solver::checkSAT() {
  for (CRef cr : constraints) {
    const Constr& C = ca[cr];
    if (C.getOrigin() == Origin::FORMULA && !C.toExpanded(cePools)->isSatisfied(getLevel())) return false;
  }
  return true;
}

Lit Solver::pickBranchLit(bool lastSolPhase) {
  Var next = 0;
  // Activity based decision:
  while (next == 0 || !isUnknown(Pos, next)) {
    if (order_heap.empty())
      return 0;
    else
      next = order_heap.removeMax();
  }
  assert(phase[0] == 0);
  assert(lastSol[0] == 0);
  return (lastSolPhase && (int)lastSol.size() > next) ? lastSol[next] : phase[next];
}

// TODO: this should be called sonething else
void Solver::presolve() {
  firstRun = false;
  if (lpSolver) {
    try {
      aux::timeCall<void>([&] { lpSolver->inProcess(); }, stats.LPTOTALTIME);
    } catch (...) {
      lpSolver.reset();
      if (options.verbosity.get() > 0) std::cout << "c Disabling crashed LP" << std::endl;
    }
  }
}

SolveState Solver::handleConflict(CeSuper confl) {
  assert(confl->hasNegativeSlack(Level));
  vDecayActivity();
  cDecayActivity();
  stats.NCONFL++;
  nconfl_to_restart--;
  nconfl_to_return--;
  if (false and stats.NCONFL % 1000 == 0 && options.verbosity.get() > 0) {
    printf("c #Conflicts: %10lld | #Constraints: %10lld\n", stats.NCONFL, (long long)constraints.size());
    if (options.verbosity.get() > 2) {
      // memory usage
      std::cout << "c total constraint space: " << ca.cap * 4 / 1024. / 1024. << "MB" << std::endl;
      std::cout << "c total #watches: ";
      long long cnt = 0;
      for (Lit l = -n; l <= n; l++) cnt += (long long)adj[l].size();
      std::cout << cnt << std::endl;
    }
  }
  if (stats.NCONFL % 100 == 0 && logger)
    logger->gc();
  if (decisionLevel() == 0) {
    if (logger) {
      confl->logInconsistency(Level, Pos, stats);
    }
    return SolveState::UNSAT;
  } else if (decisionLevel() >= (int)assumptions_lim.size()) {
    CeSuper analyzed = aux::timeCall<CeSuper>(
        [&] { return analyze(confl); },
        stats.CATIME);  // TODO: should be named differently to make clear that it came from conflict analysis
    assert(analyzed);
    assert(analyzed->hasNegativeSlack(getLevel()));
    assert(analyzed->isSaturated());
    if (learnedStack.size() > 0 && learnedStack.back()->orig == Origin::FARKAS)
      learnConstraint(analyzed, Origin::LEARNEDFARKAS);  // TODO: ugly hack (check Exact)
    else
      learnConstraint(analyzed, Origin::LEARNED);
  } else {  // conlfict with respect to assumptions (directly after assigning assumptions we propagte to conflict)
    aux::timeCall<void>([&] { extractCore(confl, assumptions); },
                              stats.CATIME);  // TODO: move time functions inside the functions
    for ([[maybe_unused]] const CeSuper& core : cores) {
      assert(core);
      assert(core->hasNegativeSlack(assumptions));
    }
    return SolveState::INCONSISTENT;
  }
  return SolveState::SOLVING;
}

SolveState Solver::makeDecision() {
  // TODO: the next block should move to the conflict, but maybe there is a reason to leave it here
  // Probably the reason is to check if we get more conflicts without making any decisions
  if (nconfl_to_restart <= 0) {
    backjumpTo(0);
    double rest_base = luby(options.lubyBase.get(), ++stats.NRESTARTS);
    nconfl_to_restart = (long long)rest_base * options.lubyMult.get();
    //        return {SolveState::RESTARTED, {}, lastSol}; // avoid this overhead for now
  }
  if (nconfl_to_return <= 0) {
    // TODO: do we really need to restart here?
    backjumpTo(0);
    nconfl_to_return = std::numeric_limits<long long>::max();
    return SolveState::INTERRUPTED;
  }
  if (stats.NCONFL >=
      (stats.NCLEANUP + 1) *
      nconfl_to_reduce) {  // TODO: this should be w.r.t. the size of the DB and not w.r.t. conflicts
    if (options.verbosity.get() > 0) puts("c INPROCESSING");  // TODO: This should be called something else
    ++stats.NCLEANUP;
    reduceDB();
    while (stats.NCONFL >= stats.NCLEANUP * nconfl_to_reduce) nconfl_to_reduce += options.dbCleanInc.get();
    if (lpSolver) {
      try {
        aux::timeCall<void>([&] { lpSolver->inProcess(); }, stats.LPTOTALTIME);
      } catch (...) {
        lpSolver.reset();
        if (options.verbosity.get() > 0) std::cout << "c Disabling crashed LP" << std::endl;
      }
    }
    return SolveState::INPROCESSED;
  }
  Lit next = 0;
  if ((int)assumptions_lim.size() > decisionLevel() + 1) assumptions_lim.resize(decisionLevel() + 1);
  if (assumptions_lim.back() < (int)assumptions.size()) {
    for (int i = (decisionLevel() == 0 ? 0 : trail_lim.back()); i < (int)trail.size(); ++i) {
      Lit l = trail[i];
      if (assumptions.has(-l)) {  // found conflicting assumption
        if (isUnit(Level, l)) {   // negated assumption is unit
                                  // TODO: this unit core should be handled properly
          backjumpTo(0);
          cores = {cePools.take32()};
        } else {
          aux::timeCall<void>(
              [&] { extractCore(ca[Reason[toVar(l)]].toExpanded(cePools), assumptions, -l); }, stats.CATIME);
          for ([[maybe_unused]] const CeSuper& core : cores) {
            assert(core);
            assert(core->hasNegativeSlack(assumptions));
          }
        }
        return SolveState::INCONSISTENT;
      }
    }
  }
  while (assumptions_lim.back() < (int)assumptions.size()) {
    assert(decisionLevel() == (int)assumptions_lim.size() - 1);
    Lit l_assump = assumptions.getKeys()[assumptions_lim.back()];
    assert(!isFalse(Level, l_assump));  // otherwise above check should have caught this
    if (isTrue(Level, l_assump)) {      // assumption already propagated
      ++assumptions_lim.back();
    } else {  // unassigned assumption
      next = l_assump;
      assumptions_lim.push_back(assumptions_lim.back() + 1);
      break;
    }
  }
  if (next == 0) next = pickBranchLit(assumptions.isEmpty() && options.cgSolutionPhase);
  if (next == 0) {  // TODO: found SAT
    assert(order_heap.empty());
    assert((int)trail.size() == getNbVars());
    assert(checkSAT());
    lastSol.clear();
    // We want to keep track of the full solution for e.g. branching heuristics based on last found solution
    lastSol.resize(getNbVars() + 1);
    lastSol[0] = 0;
    for (Var v = 1; v <= getNbVars(); ++v) lastSol[v] = isTrue(Level, v) ? v : -v;
    backjumpTo(0);
    return SolveState::SAT;
  }
  decide(next);
  return SolveState::SOLVING;
}

SolveAnswer Solver::solve() {
  if (firstRun) presolve();
  assumptions_lim = {0};
  assumptions_lim.reserve((int)assumptions.size() + 1);
  bool runLP = false;
  while (true) {
    // Test for interrupts.
    if (asynch_interrupt) throw asynchInterrupt;
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get()) throw timeoutInterrupt;

    CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(runLP); }, stats.PROPTIME);
    runLP = !confl;
    enum SolveState state;
    if (confl) {
      state = handleConflict(confl);
    } else {
      state = makeDecision();
    }
    switch(state) {
    case SolveState::SOLVING:
      break;
    case SolveState::SAT:
    case SolveState::INPROCESSED:
    case SolveState::UNSAT:
    case SolveState::RESTARTED:
    case SolveState::INTERRUPTED:
      return {state, {}, lastSol};
    case SolveState::INCONSISTENT:
      // Leave cores empty for next call
      std::vector<CeSuper> result;
      std::swap(result, cores);
      return {SolveState::INCONSISTENT, result, lastSol};
    }
  }
}

}  // namespace rs

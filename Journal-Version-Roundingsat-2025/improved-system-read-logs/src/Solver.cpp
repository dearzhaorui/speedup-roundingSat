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
#include <cinttypes>  // for counting memory usage in the methods from Cadical

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
  assert(C.getOrigin() == Origin::LOWERBOUND || C.getOrigin() == Origin::UPPERBOUND);
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
  //if (options.verbosity.get() > 0) puts("c GARBAGE COLLECT");
  std::cout << "GC " << std::flush;

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
void Solver::reduceDB_read() {
  static std::vector<bool> rm; rm.resize(crefID+1, false);
  static std::vector<ID> removedIDs; removedIDs.clear();
  assert(iID == (int)constraints.size());
  assert(iID == (int)slackMCoefV.size());
  
  nconfl_to_reduce = nextCleanupInfo.nCfReduce; // this is updated in cleanups
  for (auto& id : nextCleanupInfo.IDs) {
    assert(id <= crefID);
    rm[id] = true;
    removedIDs.push_back(id);
  }
  
  std::vector<int> oldId2NewId(iID, -1);
  iID = 0;
  uint k = 0;
  for (CRef& cr : constraints) {
    Constr& C = ca[cr];
    if (rm[C.id]) {removeConstraintWithIID(k, true); } // the old objective ctrs may be marked to be removed after finding a new solution
    if (!slackMCoefV[k].removed) oldId2NewId[k] = iID++;
    ++k;
  }
  
  // update watch lists
  for (Lit l = -n; l <= n; ++l) {
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (slackMCoefV[adj[l][i].iID].removed) {swapErase_watches(adj[l], i--);} // for clauses and cards, this iID is also needed, it's for their deletion info here
      else {
        adj[l][i].iID = oldId2NewId[adj[l][i].iID];
        assert(adj[l][i].iID > -1);
      }
    }
  }

#define update_iID(iid) iid = oldId2NewId[iid];
  for (auto& p : lowerUpperBoundCtrIID) {assert(p.second != -1); update_iID(p.second); }
#undef update_iID

  size_t i = 0;
  size_t j = 0;
  for (; i < constraints.size(); ++i) {
    if (slackMCoefV[i].removed) {
      slackMCoefV[i].clear(); // explicitly destory the ptr 
      assert(oldId2NewId[i] == -1);
      Constr& c = ca[constraints[i]];
      ca.wasted += c.getMemSize();
      c.freeUp();  // free up indirectly owned memory before implicitly deleting c during garbage collect
    } else {
      assert(oldId2NewId[i] >= 0);
      constraints[j] = constraints[i];
      slackMCoefV[j] = slackMCoefV[i];
      ++j;
    }
  }
  assert(slackMCoefV.size() == oldId2NewId.size());
  
  constraints.resize(j);
  slackMCoefV.resize(j);
  assert(iID == (int)slackMCoefV.size());
  
  if (nextCleanupInfo.GC) garbage_collect();
  for(ID id : removedIDs) rm[id] = false;
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

 // read from queues
void Solver::readLemma( const Ce32& input) {
   Lemma& lem = lemmas.front();
  assert(input->isReset());
  for (uint i = 0; i < lem.termsV.size(); ++i) {
    const auto& terms = lem.termsV[i];
    for(const auto&t : terms) input->addLhs(t.c, t.l);
    input->addRhs(lem.degreeV[i]);
    input->orig = Origin(lem.origV[i]);
    learnedStack.push_back(input->toSimple());
    input->reset();
  }
  lemmas.pop();
}

 // read from queues
void Solver::readCores( const Ce32& input, std::vector<CeSuper>& result) {
  result.clear();
  assert(input->isReset());
  const CoreCe& ce = coreCes.front();
  stats.NDECIDE = ce.rDecs; // extractCore will also increase decisions
  for (uint i = 0; i < ce.termsV.size(); ++i) {
    const auto& terms = ce.termsV[i];
    for(const auto&t : terms) input->addLhs(t.c, t.l);
    input->addRhs(ce.degreeV[i]);
    input->orig = Origin(ce.origV[i]);
    result.push_back(input->clone(cePools)); // clone decides the coef type
    input->reset();
  }
  coreCes.pop();
}

void Solver::initLogReader(std::string nameFile) {
  assert(options.readFile);
  logReader = std::make_shared<rs::File>(this, nameFile);
}

SolveState Solver::readLemmas(CeSuper confl, const Ce32& input, std::vector<CeSuper>& result) {
  stats.NCONFL++;
  nconfl_to_restart--;
  nconfl_to_return--;
  
  if (decisionLevel() == 0) { // return UNSAT
    if (logger) {
      confl->logInconsistency(Level, Pos, stats);
    }
    lemmas.pop();
    return SolveState::UNSAT;
  } 
  else if (nextConfForCoreLem != stats.NCONFL) {  // Analyse: read lemm
    assert(lemmas.front().termsV.size() == 1);
    readLemma(input);
  } 
  else { // conflicting, extractCore
    if (!confCoreLem.empty()) {nextConfForCoreLem = confCoreLem.front(); confCoreLem.pop();}
    backjumpTo(0);
    readLemma(input);
    readCores(input, result);
    return SolveState::INCONSISTENT;
  }
  return SolveState::SOLVING;
}

SolveState Solver::readDecision(const Ce32& input, std::vector<CeSuper>& result) {
  if (nconfl_to_restart <= 0) {
    backjumpTo(0);
    double rest_base = luby(options.lubyBase.get(), ++stats.NRESTARTS);
    nconfl_to_restart = (long long)rest_base * options.lubyMult.get();
    std::cout << "R" << std::flush;
  }
  if (nconfl_to_return <= 0) {
    // TODO: do we really need to restart here?
    backjumpTo(0);
    nconfl_to_return = std::numeric_limits<long long>::max();
    return SolveState::INTERRUPTED;
  }
  if (stats.NCONFL >= (stats.NCLEANUP + 1) * nconfl_to_reduce) {  // TODO: this should be w.r.t. the size of the DB and not w.r.t. conflicts
    ++stats.NCLEANUP;
    std::cout << "C" << stats.NCLEANUP << " " << std::flush;
    assert(!nextCleanupInfo.isReset());
    assert((int)trail.size() == nextCleanupInfo.trailSize);
    reduceDB_read();
    nextCleanupInfo.reset();
    logReader->readUntilNextCleanup(); 
    // because we don't process the assumptions_lim when reading a decision from logs, 
    // we need this value(#conflicts) to tell solver what to when finding a conflict
    if (!confCoreLem.empty()) {nextConfForCoreLem = confCoreLem.front(); confCoreLem.pop();}
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
  if(allDecisions.size() == 0) {std::cout << "All decisions have been read!" << std::endl; return SolveState::INTERRUPTED;}
  next = allDecisions.front();
  allDecisions.pop();
  
  if (next == 0) {
    assert(!direct0s.empty());
    char c = direct0s.front();
    direct0s.pop();
    
    if (c != 's') { // found conflicting assumption
      backjumpTo(0);
      if (c == 'p') { // p->found an unit in last DL
        result.clear();
        result = {cePools.take32()};
      }
      else { // no conflict, extractCore
        assert(c == 'l' or c == 'r');  // l->lemmas learned in extractCore, r->cores
        readLemma(input);
        readCores(input, result);
      }
      return SolveState::INCONSISTENT;
    }
    // s->solution_found
    order_heap.clear();
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

/* we focus on the optimization problems, keeping this method here 
only for avoiding the problem when it's called for solving satisfiability problems
*/
SolveAnswer Solver::solve() {
  std::cout << "Indenpendently running RoundingSat is not supported in this system!!" << std::endl;
  exit(0);
  return {SolveState::INCONSISTENT, {cePools.take32()}, lastSol};
}

//// Default options are:
//./roundingsat --r=1 --prop-counting=0.6 --exec=log-file.gz ~/opb-478/*.opb

SolveAnswer Solver::solve_read() {
  if (firstRun) presolve();
  bool runLP = false;
  assert(slackMCoefV.size() == constraints.size());
  assert((int)slackMCoefV.size() == iID);
  Ce32 input = cePools.take32(); // take<int, long long>
  std::vector<CeSuper> result;
  
  while (true) {
    // Test for interrupts.
    if (asynch_interrupt) throw asynchInterrupt;
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get()) throw timeoutInterrupt;

    CeSuper confl = aux::timeCall<CeSuper>([&] { return runPropagation(runLP); }, stats.PROPTIME);
    runLP = !confl;
    enum SolveState state;
    if (confl) {
      order_heap.clear(); // only for reading
      if (lemmas.size() == 0) {std::cout << "\nall lemmas have been read!\n" << std::flush; state = SolveState::INTERRUPTED;}
      else {
        state = readLemmas(confl, input, result);
      }
    } 
    else { // NO conflict
      state = readDecision(input, result);
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
      return {SolveState::INCONSISTENT, result, lastSol};
    }
  }
}

// Debug method
bool Solver::checkAllCtrPropagated() {
  for(int i = 0; i < (int)constraints.size(); ++i) {
    if (slackMCoefV[i].removed) continue;
    Constr& C = ca[constraints[i]];
    C.allLitsPropagated(*this, i);
  }
  return true;
}

// Methods from Cadical
int64_t Solver::maximum_resident_set_size () {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  return (((uint64_t) u.ru_maxrss) << 10)/((double)(1l<<20)); // m/(double)(1l<<20)
}

int64_t Solver::current_resident_set_size () {
  char path[40];
  sprintf (path, "/proc/%" PRId64 "/statm", (int64_t) getpid ());
  FILE * file = fopen (path, "r");
  if (!file) return 0;
  uint64_t dummy, rss;
  int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? (rss * sysconf (_SC_PAGESIZE))/((double)(1l<<20)) : 0;
}

}  // namespace rs

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

#include "Solver.hpp"
#include <cmath>
#include "aux.hpp"
#include "globals.hpp"

// ---------------------------------------------------------------------
// Initialization

Solver::Solver() : order_heap(activity) {
  ca.memory = NULL;
  ca.at = 0;
  ca.cap = 0;
  ca.wasted = 0;
  ca.capacity(1024 * 1024);  // 4MB
  assert(sizeof(Constr) == 10 * sizeof(uint32_t));
}

void Solver::setNbVars(long long nvars) {
  assert(nvars > 0);
  assert(nvars < INF);
  if (nvars <= n) return;
  aux::resizeIntMap(_adj, adj, nvars, options.resize_factor, {});
  aux::resizeIntMap(_Level, Level, nvars, options.resize_factor, INF);
  Pos.resize(nvars + 1, INF);
  Reason.resize(nvars + 1, CRef_Undef);
  activity.resize(nvars + 1, 1 / actLimitV);
  phase.resize(nvars + 1);
  tmpConstraint.resize(nvars + 1);
  conflConstraint.resize(nvars + 1);
  logConstraint.resize(nvars + 1);
  order_heap.resize(nvars + 1);
  for (Var v = n + 1; v <= nvars; ++v) phase[v] = -v, order_heap.insert(v);
  n = nvars;
  stats.NAUXVARS = n - orig_n;
}

void Solver::setNbOrigVars(int o_n) {
  orig_n = o_n;
  stats.NAUXVARS = n - orig_n;
}

void Solver::init() {
  if (!options.proofLogName.empty()) logger = std::make_shared<Logger>(options.proofLogName);
  tmpConstraint.initializeLogging(logger);
  conflConstraint.initializeLogging(logger);
  logConstraint.initializeLogging(logger);
}

// ---------------------------------------------------------------------
// VSIDS

void Solver::vDecayActivity() { v_vsids_inc *= (1 / options.v_vsids_decay); }
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

void Solver::cDecayActivity() { c_vsids_inc *= (1 / options.c_vsids_decay); }
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
  Var v = std::abs(p);
  Reason[v] = from;
  if (decisionLevel() == 0) {
    Reason[v] = CRef_Undef;  // no need to keep track of reasons for unit literals
    if (logger) {
      Constr& C = ca[from];
      C.toConstraint(logConstraint);
      logConstraint.logUnit(Level, Pos, v, stats);
      logConstraint.reset();
      assert(logger->unitIDs.size() == trail.size() + 1);
    }
  }
  Level[p] = decisionLevel();
  Pos[v] = (int)trail.size();
  trail.push_back(p);
}

void Solver::undoOne() {
  assert(!trail.empty());
  ++stats.NTRAILPOPS;
  Lit l = trail.back();
  if (qhead == (int)trail.size()) {
    for (const Watch& w : adj[-l])
      if (w.isPB()) {  // Counter or watched
        assert(ca[constraints[w.iID]].isCounting() || ca[constraints[w.iID]].isWatched(w.idx));
        assert(!options.oldProp);
        ++stats.NWATCHLOOKUPSBJ;
        slackMM[w.iID] += abs(w.coeffOfLit());
      }
    --qhead;
  }
  Var v = std::abs(l);
  trail.pop_back();
  Level[l] = INF;
  Pos[v] = INF;
  phase[v] = l;
  if (!trail_lim.empty() && trail_lim.back() == (int)trail.size()) trail_lim.pop_back();
  order_heap.insert(v);
}

void Solver::backjumpTo(int level) {
  assert(level >= 0);
  while (decisionLevel() > level) undoOne();
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

#define minsumwatch ntrailpops
#define nwatch watchIdx
#define oldmarker std::numeric_limits<int>::min()
/**
 * Unit propagation with watched literals.
 * @post: all watches up to trail[qhead] have been propagated
 */

// use two pointers when deleting watchList elements
bool Solver::runPropagation() { // 2 pointers
  bool conflict = false; 
  while (qhead < (int)trail.size()) {
    Lit p = trail[qhead++];
    std::vector<Watch>& ws = adj[-p];
    
    const auto end = ws.end();
    auto itWL = ws.begin();
    auto itWL_kept = itWL; 
    while (itWL != end) {
      Watch& w = *itWL_kept++ = *itWL++;
      int idx = w.idx;
      if (idx < 0 && idx != oldmarker && ( (idx < -1 && isTrue(Level, idx + INF)) // logn clause
                                        || (idx == -1 && isTrue(Level, w.otherBinLit()))  )) { // Binary
        assert(ca[constraints[w.iID]].isClause());
        continue;
      }  // blocked literal check
      
      WatchStatus wstat = checkForPropagation(w, -p);
      if (wstat == WatchStatus::DROPWATCH)
        itWL_kept--;
      else if (wstat == WatchStatus::CONFLICTING) {  // clean up current level and stop propagation
        ++stats.NTRAILPOPS;
        auto itWL_visited = ws.begin();
        while(itWL_visited != itWL_kept) {
          const Watch& w = *itWL_visited++;
          if (w.isPB()) {  // Counter or watched
            assert(ca[constraints[w.iID]].isCounting() || ca[constraints[w.iID]].isWatched(w.idx));
            assert(!options.oldProp);
            ++stats.NWATCHLOOKUPSBJ;
            slackMM[w.iID] += abs(w.coeffOfLit());
          }
        }
        --qhead;
        
        Constr& C = ca[constraints[w.iID]];
        if (C.getType() == ConstraintType::LEARNT) {
          cBumpActivity(C);
          recomputeLBD(C);
        }
        C.toConstraint(conflConstraint);
        conflict = true;
        break;
      }
    }
    
    if (itWL_kept != itWL) {
      while(itWL != end) {
        *itWL_kept++ = *itWL++;
      }
      ws.resize(itWL_kept - ws.begin(), Watch());  // numElems, keep the allocatedInts
    }
    
    if(conflict) break;
  }
  return !conflict;
}

WatchStatus Solver::checkForPropagation(Watch& watch, Lit p) {
  const uint32_t iID = watch.iID;

  assert(isFalse(Level, p));
  ++stats.NWATCHLOOKUPS;

  if (watch.isBin()) {
    assert(ca[constraints[iID]].isClause() && ca[constraints[iID]].size()==2);
    Lit other = watch.otherBinLit();
    assert(!isTrue(Level, other));
    if (isUnknown(Pos, other)) {
      ++stats.NPROPCLAUSE;
      propagate(other, constraints[iID]);
    }
    else if (isFalse(Level, other)) {
      return WatchStatus::CONFLICTING;
    }
    ++stats.NPROPCHECKS;
    return WatchStatus::KEEPWATCH;
  }
  
  if (watch.isClause()) {
    CRef& cr = constraints[iID];
    Constr& C = ca[cr];
    int* data = C.data;
    assert(C.isClause());
    
    int& idx = watch.idx;
    Lit l0 = data[0]; Lit l1 = data[1];
    assert(idx < 0);
    assert(p == l0 || p == l1);
    assert(C.size() > 1);
    int widx = 0;
    Lit watch = l0;
    Lit otherwatch = l1;
    if (p == l1) {
      widx = 1;
      watch = l1;
      otherwatch = l0;
    }
    assert(p == watch);
    assert(p != otherwatch);
    
    if (isTrue(Level, otherwatch)) {
      idx = otherwatch - INF;         // set new blocked literal
      return WatchStatus::KEEPWATCH;  // constraint is satisfied
    }
    const unsigned int Csize = C.size();
    for (unsigned int i = 2; i < Csize; ++i) {
      Lit l = data[i];
      if (!isFalse(Level, l)) {
        int mid = i / 2 + 1;
        data[i] = data[mid];
        data[mid] = watch;
        data[widx] = l;
        adj[l].emplace_back(iID, otherwatch - INF, 0);
        stats.NWATCHCHECKS += i - 1;
        return WatchStatus::DROPWATCH;
      }
    }
    stats.NWATCHCHECKS += Csize - 2;
    assert(isFalse(Level, watch));
    for (unsigned int i = 2; i < Csize; ++i) assert(isFalse(Level, data[i]));
    if (isFalse(Level, otherwatch))
      return WatchStatus::CONFLICTING;
    else {
      assert(!isTrue(Level, otherwatch));
      ++stats.NPROPCLAUSE;
      propagate(otherwatch, cr);
    } 
    ++stats.NPROPCHECKS;
    return WatchStatus::KEEPWATCH;
  }

  if (watch.isCard()) {
    CRef& cr = constraints[iID];
    Constr& C = ca[cr];
    int* data = C.data;
    assert(C.isCard());
    
    int widx = watch.idx;
    assert(widx >= 0 && widx % 2 == 1);
    widx = widx >> 1;
    assert(data[widx] == p);
    const unsigned int Csize = C.size();
    const Val degree = C.degree;
    uint lidx = degree + 1;
    if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS) 
      C.ntrailpops = stats.NTRAILPOPS;
    else lidx = C.watchIdx;
    
    assert(lidx > degree);
    stats.NWATCHCHECKS -= lidx;
    for (; lidx < Csize; ++lidx) {
      Lit l = data[lidx];
      if (!isFalse(Level, l)) {
        unsigned int mid = (lidx + degree + 1) / 2;
        assert(mid <= lidx);
        assert(mid > degree);
        data[lidx] = data[mid];
        data[mid] = data[widx];
        data[widx] = l;
        adj[l].emplace_back(iID, (widx << 1) + 1, 1);
        C.watchIdx = lidx;
        stats.NWATCHCHECKS += lidx + 1;
        return WatchStatus::DROPWATCH;
      }
    }
    assert(lidx == Csize);
    C.watchIdx = lidx;
    stats.NWATCHCHECKS += lidx;
    assert(isFalse(Level, data[widx]));
    for (unsigned int i = degree + 1; i < Csize; ++i) assert(isFalse(Level, data[i]));
    for (int i = 0; i <= degree; ++i)
      if (i != widx && isFalse(Level, data[i])) return WatchStatus::CONFLICTING;
    for (int i = 0; i <= degree; ++i) {
      Lit l = data[i];
      if (i != widx && !isTrue(Level, l)) {
        ++stats.NPROPCARD;
        propagate(l, cr);
      }
    }
    stats.NPROPCHECKS += degree + 1;
    return WatchStatus::KEEPWATCH;
  }

  if (options.oldProp) {
    CRef cr = constraints[watch.iID];
    Constr& C = ca[cr];
    int* data = C.data;
    
    unsigned int watchIdx = C.watchIdx;
    int* lits = data;
    int* coefs = data + C.size();
    bool watchlocked = false;
    assert(trail[qhead - 1] == -p);
    for (unsigned int i = 0; i < nwatch && !watchlocked; i++) {
      int l = lits[i];
      if (isFalse(getLevel(), l) && Pos[std::abs(l)] < qhead - 1) watchlocked = true;
    }
    if (!watchlocked) {
      int pos = 0;
      while (lits[pos] != p) pos++;
      int c = coefs[pos];
      unsigned int it = nwatch;
      stats.NWATCHCHECKS -= it;
      long long sumwatchcoefs = slackMM[iID];
      for (; it < C.size() && sumwatchcoefs - c < C.minsumwatch; it++) {
        int l = lits[it];
        if (!isFalse(getLevel(), l)) {
          int cf = coefs[it];
          sumwatchcoefs += cf;
          coefs[it] = coefs[C.nwatch];
          coefs[C.nwatch] = cf;
          lits[it] = lits[C.nwatch];
          lits[C.nwatch] = l;
          adj[l].emplace_back(iID, oldmarker, 0);
          C.nwatch++;
        }
      }
      stats.NWATCHCHECKS += it;
      if (sumwatchcoefs - c >= C.minsumwatch) {
        std::swap(lits[pos], lits[C.nwatch - 1]), std::swap(coefs[pos], coefs[C.nwatch - 1]);
        sumwatchcoefs -= coefs[C.nwatch - 1];
        C.nwatch--;
        slackMM[iID] = sumwatchcoefs;
        return WatchStatus::DROPWATCH;
      }
      slackMM[iID] = sumwatchcoefs;
    }

    const Val degree = C.degree;
    long long s = -degree;
    for (unsigned int i = 0; i < C.nwatch; i++)
      if (!isFalse(getLevel(), lits[i])) s += coefs[i];

    if (s < 0) return WatchStatus::CONFLICTING;
    for (unsigned int it = 0; it < C.nwatch; it++) {
      int l = lits[it];
      if (coefs[it] > s && isUnknown(getPos(), l)) {
        stats.NPROPCLAUSE += (degree == 1);
        stats.NPROPCARD += (degree != 1 && C.minsumwatch - degree == 1);
        ++stats.NPROPWATCH;
        propagate(l, cr);
      }
    }
    stats.NPROPCHECKS += C.nwatch;
    return WatchStatus::KEEPWATCH;
  }

  assert(watch.isPB());
  assert(!ca[constraints[iID]].isSimple());
  assert(ca[constraints[iID]].data[watch.idx + 1] == p);
  
  Coef c = watch.coeffOfLit();
  
  if (c > 0) {  // use counting propagation
    assert(ca[constraints[iID]].isCounting());
    Val& snfMC = slackMM[iID];
    snfMC -= c;
    
    if (snfMC < 0) {
      CRef& cr = constraints[iID];
      Constr& C = ca[cr];
      const Coef ClargestCoef = C.largestCoef();
      Val slack = snfMC + ClargestCoef;
      if (slack < 0) return WatchStatus::CONFLICTING;
      
      int* data = C.data;
      const unsigned int Csize2 = 2 * C.size();
      uint lidx = 0;
      if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS)
        C.ntrailpops = stats.NTRAILPOPS;
      else lidx = C.watchIdx;
      
      const Val degree = C.degree;
      stats.NPROPCHECKS -= lidx >> 1;
      for (; lidx < Csize2 && data[lidx] > slack; lidx += 2) {
        const Lit l = data[lidx + 1];
        if (isUnknown(Pos, l)) {
          stats.NPROPCLAUSE += (degree == 1);
          stats.NPROPCARD += (degree != 1 && ClargestCoef == 1);
          ++stats.NPROPCOUNTING;
          propagate(l, cr);
        }
      }
      C.watchIdx = lidx;
      stats.NPROPCHECKS += lidx >> 1;
    }
    return WatchStatus::KEEPWATCH;
  }

  // use watched propagation
  assert(ca[constraints[iID]].isWatchedPB());
  Val snfMC = slackMM[iID];
  CRef& cr = constraints[iID];
  Constr& C = ca[cr];
  int* data = C.data;
  uint lidx = C.watchIdx;
  
  assert(c < 0);
  c = -c;
  snfMC -= c;
  
  if (!options.supProp || snfMC + c >= 0) {  // look for new watches if previously, slack was at least ClargestCoef
    uint start_lidx = lidx;
    stats.NWATCHCHECKS -= lidx >> 1;
    const unsigned int Csize2 = 2 * C.size();
    for (; snfMC < 0 && lidx < Csize2; lidx += 2) { 
      const Coef cf = data[lidx];
      const Lit l = data[lidx + 1];
      if (cf > 0 && !isFalse(Level, l)) {
        snfMC += cf;
        data[lidx] = -cf;
        adj[l].emplace_back(iID, lidx, -cf);
      }
    }
    stats.NWATCHCHECKS += lidx >> 1;
    
    if (snfMC < 0 && C.ntrailpops < stats.NTRAILPOPS) { // need second search starting at the head?
      C.ntrailpops = stats.NTRAILPOPS;
      lidx = 0;
      for (; snfMC < 0 && lidx < start_lidx; lidx += 2) {
        const Coef cf = data[lidx];
        const Lit l = data[lidx + 1];
        if (cf > 0 && !isFalse(Level, l)) {
          snfMC += cf;
          data[lidx] = -cf;
          adj[l].emplace_back(iID, lidx, -cf);
        }
      }
      stats.NWATCHCHECKS += lidx >> 1;
    }
    
    if (snfMC < 0)
      lidx = 0;
    
    C.watchIdx = lidx;
  }  // else we did not find enough watches last time, so we can skip looking for them now

  slackMM[iID] = snfMC;
  
  if (snfMC >= 0) {
    data[watch.idx] = c;
    return WatchStatus::DROPWATCH;
  }
  const Coef ClargestCoef = C.largestCoef();
  Val slack = snfMC + ClargestCoef;
  if (slack < 0) {
    return WatchStatus::CONFLICTING;
  }
  
  const unsigned int Csize2 = 2 * C.size();
  // keep the watch, check for propagation
  const Val degree = C.degree;
  if (!options.idxProp || C.ntrailpops < stats.NTRAILPOPS) {
    C.ntrailpops = stats.NTRAILPOPS;
    lidx = 0;
  }
  
  stats.NPROPCHECKS -= lidx >> 1;
  for (; lidx < Csize2 && std::abs(data[lidx]) > slack; lidx += 2) {  // NOTE: second innermost loop of RoundingSat
    const Lit l = data[lidx + 1];
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (degree == 1);
      stats.NPROPCARD += (degree != 1 && ClargestCoef == 1);
      ++stats.NPROPWATCH;
      propagate(l, cr);
    }
  }
  C.watchIdx = lidx;
  stats.NPROPCHECKS += lidx >> 1;
  return WatchStatus::KEEPWATCH;
  
}

// ---------------------------------------------------------------------
// Conflict analysis

void Solver::recomputeLBD(Constr& C) {
  unsigned int lbd = C.lbd();
  if (lbd > 2) {  // constraints with LBD <= 2 won't have score recomputed
    assert(tmpSet.size() == 0);
    const int Csize = (int)C.size();
    for (int i = 0; i < Csize; i++)
      if (isFalse(Level, C.lit(i))) tmpSet.add(Level[-C.lit(i)]);
    if (lbd > tmpSet.size() + 1) C.setLBD(tmpSet.size());  // simulate Glucose
    tmpSet.reset();
  }
}

bool Solver::analyze() {
  if (logger) logger->logComment("analyzing", stats);
  assert(conflConstraint.getSlack(Level) < 0);
  stats.NADDEDLITERALS += conflConstraint.vars.size();
  conflConstraint.removeUnitsAndZeroes(Level, Pos);
  assert(actSet.size() == 0);  // will hold the literals that need their activity bumped
  for (Var v : conflConstraint.vars) actSet.add(conflConstraint.getLit(v));
  while (decisionLevel() > 0) {
    if (asynch_interrupt) return false;
    Lit l = trail.back();
    assert(std::abs(conflConstraint.getCoef(-l)) < INF);
    Coef confl_coef_l = conflConstraint.getCoef(-l);
    if (confl_coef_l > 0) {
      ++stats.NRESOLVESTEPS;
      assert(conflConstraint.getSlack(Level) < 0);
      AssertionStatus status = conflConstraint.isAssertingBefore(Level, decisionLevel());
      if (status == AssertionStatus::ASSERTING)
        break;
      else if (status == AssertionStatus::FALSIFIED) {
        backjumpTo(decisionLevel() - 1);
        assert(conflConstraint.getSlack(Level) < 0);
        continue;
      }
      assert(Reason[std::abs(l)] != CRef_Undef);
      Constr& reasonC = ca[Reason[std::abs(l)]];
      if (reasonC.getType() == ConstraintType::LEARNT) {
        cBumpActivity(reasonC);
        recomputeLBD(reasonC);
      }
      reasonC.toConstraint(tmpConstraint);
      stats.NADDEDLITERALS += tmpConstraint.vars.size();
      tmpConstraint.removeUnitsAndZeroes(Level, Pos);  // NOTE: also saturates
      if (options.weakenNonImplying)
        tmpConstraint.weakenNonImplying(Level, tmpConstraint.getCoef(l), tmpConstraint.getSlack(Level),
                                        stats);  // NOTE: also saturates
      assert(tmpConstraint.getCoef(l) > tmpConstraint.getSlack(Level));
      tmpConstraint.weakenDivideRound(getLevel(), l, options.maxdiv, options.weakenFull);
      assert(tmpConstraint.getSlack(Level) <= 0);
      for (Var v : tmpConstraint.vars) actSet.add(tmpConstraint.getLit(v));
      Coef reason_coef_l = tmpConstraint.getCoef(l);
      Coef gcd_coef_l = aux::gcd(reason_coef_l, confl_coef_l);
      conflConstraint.addUp(tmpConstraint, confl_coef_l / gcd_coef_l, reason_coef_l / gcd_coef_l);
      conflConstraint.saturateAndFixOverflow(getLevel(), options.weakenFull);
      tmpConstraint.reset();
      assert(conflConstraint.getCoef(-l) == 0);
      assert(conflConstraint.getSlack(Level) < 0);
    }
    undoOne();
  }
  assert(conflConstraint.getSlack(Level) < 0);
  for (Lit l : actSet.keys)
    if (l != 0) vBumpActivity(std::abs(l));
  actSet.reset();
  return true;
}

bool Solver::extractCore(const IntSet& assumptions, intConstr& outCore, Lit l_assump) {
  assert(!conflConstraint.isReset());
  outCore.reset();

  if (l_assump != 0) {  // l_assump is an assumption propagated to the opposite value
    assert(assumptions.has(l_assump));
    assert(isFalse(Level, l_assump));
    int pos = Pos[std::abs(l_assump)];
    while ((int)trail.size() > pos) undoOne();
    assert(isUnknown(Pos, l_assump));
    decide(l_assump);
  }

  // Set all assumptions in front of the trail, all propagations later. This makes it easy to do decision learning.
  // For this, we first copy the trail, then backjump to 0, then rebuild the trail.
  // Otherwise, reordering the trail messes up the slacks of the watched constraints (see undoOne()).
  std::vector<Lit> decisions;  // holds the decisions
  decisions.reserve(decisionLevel());
  std::vector<Lit> props;  // holds the propagations
  props.reserve(trail.size());
  assert(trail_lim.size() > 0);
  for (int i = trail_lim[0]; i < (int)trail.size(); ++i) {
    Lit l = trail[i];
    if (assumptions.has(l))
      decisions.push_back(l);
    else
      props.push_back(l);
  }
  backjumpTo(0);

  for (Lit l : decisions) decide(l);
  for (Lit l : props) propagate(l, Reason[std::abs(l)]);

  stats.NADDEDLITERALS += conflConstraint.vars.size();
  conflConstraint.removeUnitsAndZeroes(Level, Pos);
  assert(conflConstraint.getSlack(Level) < 0);

  // analyze conflict
  Val assumpslk = conflConstraint.getSlack(assumptions);
  while (assumpslk >= 0) {
    if (asynch_interrupt) return false;
    Lit l = trail.back();
    assert(std::abs(conflConstraint.getCoef(-l)) < INF);
    Coef confl_coef_l = conflConstraint.getCoef(-l);
    if (confl_coef_l > 0) {
      ca[Reason[std::abs(l)]].toConstraint(tmpConstraint);
      stats.NADDEDLITERALS += tmpConstraint.vars.size();
      tmpConstraint.removeUnitsAndZeroes(Level, Pos);
      if (options.weakenNonImplying)
        tmpConstraint.weakenNonImplying(Level, tmpConstraint.getCoef(l), tmpConstraint.getSlack(Level),
                                        stats);  // NOTE: also saturates
      assert(tmpConstraint.getCoef(l) > tmpConstraint.getSlack(Level));
      tmpConstraint.weakenDivideRound(getLevel(), l, options.maxdiv, options.weakenFull);
      assert(tmpConstraint.getSlack(Level) <= 0);
      Coef reason_coef_l = tmpConstraint.getCoef(l);
      Coef gcd_coef_l = aux::gcd(reason_coef_l, confl_coef_l);
      conflConstraint.addUp(tmpConstraint, confl_coef_l / gcd_coef_l, reason_coef_l / gcd_coef_l);
      conflConstraint.saturateAndFixOverflow(getLevel(), options.weakenFull);
      tmpConstraint.reset();
      assert(conflConstraint.getCoef(-l) == 0);
      assert(conflConstraint.getSlack(Level) < 0);
      assumpslk = conflConstraint.getSlack(assumptions);
    }
    assert(decisionLevel() == (int)decisions.size());
    undoOne();
  }
  assert(conflConstraint.getDegree() > 0);
  assert(conflConstraint.getDegree() < INF);
  assert(conflConstraint.isSaturated());
  conflConstraint.copyTo(outCore);
  conflConstraint.reset();

  // weaken non-falsifieds
  for (Var v : outCore.vars)
    if (!assumptions.has(-outCore.getLit(v))) outCore.weaken(-outCore.coefs[v], v);
  outCore.postProcess(Level, Pos, true, stats);
  assert(outCore.getSlack(assumptions) < 0);
  backjumpTo(0);
  return true;
}

// ---------------------------------------------------------------------
// Constraint management

CRef Solver::attachConstraint(intConstr& constraint, ConstraintType type) {
  assert(constraint.isSortedInDecreasingCoefOrder());
  assert(constraint.isSaturated());
  assert(constraint.hasNoZeroes());
  assert(constraint.hasNoUnits(Level));
  assert(constraint.getDegree() > 0);
  assert(constraint.getDegree() < INF);
  assert(constraint.vars.size() > 0);

  ++stats.NADDEDCONSTRAINTS;

  if (logger)
    constraint.logProofLineWithInfo("Attach", stats);
  else
    constraint.id = ++crefID;
    
  Val degree = constraint.getDegree();
  CRef cr = ca.alloc(constraint, type, constraint.id, degree);
  constraints.push_back(cr);
  ++iID;
  Constr& C = ca[cr];
  const unsigned int Csize = C.size();

  bool learned = type == ConstraintType::LEARNT;
  if (learned) {
    stats.LEARNEDLENGTHSUM += Csize;
    stats.LEARNEDDEGREESUM += degree;
  } else {
    stats.EXTERNLENGTHSUM += Csize;
    stats.EXTERNDEGREESUM += degree;
  }
  stats.LENGTHSUM += Csize;
  if (degree == 1) {
    stats.NCLAUSESLEARNED += learned;
    stats.NCLAUSESEXTERN += !learned;
  } else if (C.isCard() || (options.oldProp && C.ntrailpops - degree == 1) ||
             (!options.oldProp && C.largestCoef() == 1)) {
    stats.NCARDINALITIESLEARNED += learned;
    stats.NCARDINALITIESEXTERN += !learned;
  } else {
    stats.NGENERALSLEARNED += learned;
    stats.NGENERALSEXTERN += !learned;
  }

  if (C.isSimple()) {
    slackMM.push_back(0); // we don't use slack for clauses and cardinalities
    if (degree >= Csize) {
      assert(decisionLevel() == 0);
      int* data = C.data;
      for (unsigned int i = 0; i < Csize; ++i) {
        assert(isUnknown(Pos, data[i]));
        propagate(data[i], cr);
      }
      return cr;
    }

    int* data = C.data;
    unsigned int watch = 0; 
    unsigned int i = 0; 
    for (; i < Csize; ++i) {
      Lit l = data[i];
      if (!isFalse(Level, l)) {
        data[i] = data[watch];
        data[watch++] = l;
        if (watch >= degree + 1) break;
      }
    }
    
    if (watch == degree) {
      assert(i == Csize);
      assert(isFalse(Level, data[degree])); 
      for (unsigned int i = 0; i < degree; ++i) {
        Lit l = data[i];
        assert(!isFalse(Level, l));
        if (!isTrue(Level, l)) propagate(l, cr);
      }
    }
    for (int k = watch; k <= degree; k++) {
      int idxAtDegree = k;
      int dlOfLitDegree = Level[-data[idxAtDegree]];
      for (unsigned int i = degree + 1; i < Csize; ++i) {  // ensure last watch is last falsified literal
        Lit l = data[i];
        assert(isFalse(Level, l));
        if (Level[-l] > dlOfLitDegree) {
          idxAtDegree = i;
          dlOfLitDegree = Level[-l];
        }
      }
      Lit l = data[k];
      data[k] = data[idxAtDegree];
      data[idxAtDegree] = l;
    }
    assert(watch >= degree);
    
    if (C.isClause()) {
      Lit l1 = data[0]; Lit l2 = data[1];
      if (Csize == 2) { // binary
        adj[l1].emplace_back(iID-1, -1, l2);
        adj[l2].emplace_back(iID-1, -1, l1);
      }
      else {
        adj[l1].emplace_back(iID-1, l2 - INF, 0);
        adj[l2].emplace_back(iID-1, l1 - INF, 0);
      }
    }
    else {
      for (unsigned int i = 0; i <= degree; ++i) adj[data[i]].emplace_back(iID-1, (i << 1) + 1, 1); // add watch index
      C.watchIdx = std::max(i, watch); 
      assert(C.watchIdx >= degree+1);
      C.ntrailpops = stats.NTRAILPOPS;
    }
    return cr;
  }
  
  int* data = C.data;
  const unsigned int Csize2 = 2 * Csize;
  const Coef largestCoef = C.largestCoef();
  Val watchSum = -degree - largestCoef;
  unsigned int minWatches = 0;
  for (; minWatches < Csize2 && watchSum < 0; minWatches += 2) {
    watchSum += data[minWatches]; // also including false lits
  }
  minWatches >>= 1;
  assert(Csize > 0);
  assert(minWatches > 0);

  stats.WATCHSUM += minWatches;
  stats.WATCHAVG += (double)Csize / (double)minWatches;
  stats.WATCHGEO += std::log((double)Csize / (double)minWatches);

  if (options.oldProp) { // oldProp method is not changed, unless it's necessary because of the new Constraint and watchlist element structures.
    ++stats.NWATCHED;
    // sort literals by the decision level at which they were falsified, descending order (never falsified = level
    // infinity)
    std::vector<std::pair<int, unsigned int>> order;
    for (unsigned int i = 0; i < 2 * C.size(); i += 2) {
      int lvl = Level[-data[i + 1]];
      if (lvl == -1) lvl = INF;
      order.emplace_back(-lvl, i);
    }
    std::sort(order.begin(), order.end());
    std::vector<int> data_old(data, data + 2 * C.size());
    int* lits = data;
    int* coefs = data + C.size();
    for (unsigned int i = 0; i < C.size(); i++) {
      lits[i] = data_old[order[i].second + 1];
      coefs[i] = data_old[order[i].second];
    }
    long long sumwatchcoefs = 0;
    C.nwatch = 0;
    int mxcoef = 0;
    for (unsigned int i = 0; i < C.size(); i++) mxcoef = std::max(mxcoef, coefs[i]);
    C.minsumwatch = (long long)degree + mxcoef;
    for (unsigned int i = 0; i < C.size(); i++) {
      sumwatchcoefs += coefs[i];
      C.nwatch++;
      adj[lits[i]].emplace_back(iID-1, oldmarker, 0);
      if (sumwatchcoefs >= C.minsumwatch) break;
    }
    slackMM.push_back(sumwatchcoefs);

    long long s = -degree;
    for (unsigned int i = 0; i < C.nwatch; i++)
      if (!isFalse(getLevel(), lits[i])) s += coefs[i];
    assert(s >= 0);
    for (unsigned int it = 0; it < C.nwatch; it++) {
      int l = lits[it];
      if (coefs[it] > s && isUnknown(getPos(), l)) {
        stats.NPROPCLAUSE += (degree == 1);
        stats.NPROPCARD += (degree != 1 && C.minsumwatch - degree == 1);
        propagate(l, cr);
      }
    }

    return cr;
  }

  bool isCounting = (options.countingProp == 1 || options.countingProp > (1 - minWatches / (float)Csize));
  C.setCounting(isCounting);
  
  if (isCounting) {  // use counting propagation
    ++stats.NCOUNTING;
    Val slack = -degree;
    for (unsigned int i = 0; i < Csize2; i += 2) {
      Lit l = data[i + 1]; Coef c = data[i]; 
      adj[l].emplace_back(iID-1, i, c);
      if (!isFalse(Level, l) || Pos[std::abs(l)] >= qhead) slack += c;
    }
    assert(slack >= 0);
    if (slack < largestCoef) {  // propagate
      unsigned int i;
      for (i = 0; i < Csize2 && data[i] > slack; i += 2) {
        Lit l = data[i + 1];
        if (isUnknown(Pos, l)) propagate(l, cr);
      }
      C.watchIdx = i;
      C.ntrailpops = stats.NTRAILPOPS;
    }
    slackMM.push_back(slack - largestCoef);
    return cr;
  }

  // watched propagation
  ++stats.NWATCHED;
  Val slack = -degree;
  for (unsigned int i = 0; i < Csize2 && slack < largestCoef; i += 2) {
    Lit l = data[i + 1];
    if (!isFalse(Level, l) || Pos[std::abs(l)] >= qhead) {
      assert(!C.isWatched(i));
      Coef c = data[i]; 
      slack += c;
      data[i] = -c;
      adj[l].emplace_back(iID-1, i, -c);
    }
  }
  slackMM.push_back(slack - largestCoef);
  assert(slack >= 0);
  if (slack < largestCoef) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(C.size());
    for (unsigned int i = 0; i < 2 * C.size(); i += 2)
      if (isFalse(Level, data[i + 1]) && Pos[std::abs(data[i + 1])] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(),
              [&](unsigned i1, unsigned i2) { return Pos[std::abs(data[i1 + 1])] > Pos[std::abs(data[i2 + 1])]; });
    Val diff = largestCoef - slack;
    for (unsigned int i : falsifiedIdcs) {
      assert(!C.isWatched(i));
      Coef c = data[i]; 
      diff -= c;
      data[i] = -c;
      adj[data[i + 1]].emplace_back(iID-1, i, -c);
      if (diff <= 0) break;
    }
    // perform initial propagation
    unsigned int i;
    for (i = 0; i < Csize2 && std::abs(data[i]) > slack; i += 2) {
      Lit l = data[i + 1];
      if (isUnknown(Pos, l)) propagate(l, cr);
    }
    C.watchIdx = i;
    C.ntrailpops = stats.NTRAILPOPS;
  }
  return cr;
}

// NOTE: backjumps to place where the constraint is not conflicting, as otherwise we might miss propagations
CRef Solver::processLearnedStack() {
  // loop back to front as the last constraint in the queue is a result of conflict analysis
  // and we want to first check this constraint to backjump.
  while (learnedStack.size() > 0) {
    tmpConstraint.construct(learnedStack.back());
    learnedStack.pop_back();
    tmpConstraint.removeUnitsAndZeroes(Level, Pos, true);
    tmpConstraint.sortInDecreasingCoefOrder();
    int assertionLevel = tmpConstraint.getAssertionLevel(Level, Pos);
    if (assertionLevel < 0) {
      backjumpTo(0);
      assert(tmpConstraint.getSlack(Level) < 0);
      if (logger) tmpConstraint.logInconsistency(Level, Pos, stats);
      tmpConstraint.reset();
      return CRef_Unsat;
    }
    backjumpTo(assertionLevel);
    Val slk = tmpConstraint.getSlack(Level);
    assert(slk >= 0);
    tmpConstraint.heuristicWeakening(Level, Pos, slk, stats);  // TODO: don't always weaken heuristically?
    tmpConstraint.postProcess(Level, Pos, false, stats);
    assert(tmpConstraint.isSaturated());
    if (tmpConstraint.getDegree() <= 0) {
      tmpConstraint.reset();
      continue;
    }
    CRef cr = attachConstraint(tmpConstraint, ConstraintType::LEARNT);
    assert(cr != CRef_Unsat);
    tmpConstraint.reset();
    Constr& C = ca[cr];
    if (assertionLevel < INF) recomputeLBD(C);  // some constraints are not asserting so their LBD's are unknown
  }
  return CRef_Undef;
}

ID Solver::addInputConstraint(ConstraintType type) {
  assert(decisionLevel() == 0);
  if (logger) tmpConstraint.logAsInput();
  tmpConstraint.postProcess(Level, Pos, true, stats);
  assert(tmpConstraint.getDegree() < INF);
  if (tmpConstraint.getDegree() <= 0) {
    tmpConstraint.reset();
    return ID_Undef;  // already satisfied.
  }

  if (tmpConstraint.getSlack(Level) < 0) {
    if (options.verbosity > 0) puts("c Inconsistent input constraint");
    if (logger) tmpConstraint.logInconsistency(Level, Pos, stats);
    tmpConstraint.reset();
    assert(decisionLevel() == 0);
    return ID_Unsat;
  }

  CRef cr = attachConstraint(tmpConstraint, type);
  tmpConstraint.reset();
  if (!runPropagation()) {
    if (options.verbosity > 0) puts("c Input conflict");
    if (logger) {
      conflConstraint.logInconsistency(Level, Pos, stats);
      conflConstraint.reset();
    }
    assert(decisionLevel() == 0);
    return ID_Unsat;
  }
  ID id = ca[cr].id;
  if (type == ConstraintType::EXTERNAL) external[id] = cr;
  return id;
}

ID Solver::addConstraint(const intConstr& c, ConstraintType type) {
  // NOTE: copy to tmpConstraint guarantees original constraint is not changed and does not need logger
  c.copyTo(tmpConstraint);
  ID result = addInputConstraint(type);
  return result;
}

ID Solver::addConstraint(const SimpleConsInt& c, ConstraintType type) {
  tmpConstraint.construct(c);
  ID result = addInputConstraint(type);
  return result;
}

void Solver::dropExternal(ID id) {
  if (id == ID_Undef) return;
  auto old_it = external.find(id);
  assert(old_it != external.end());
  Constr& constr = ca[old_it->second];
  constr.setType(ConstraintType::AUXILIARY);
  external.erase(old_it);
}

// ---------------------------------------------------------------------
// Garbage collection

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are deleted.
void Solver::garbage_collect(const std::vector<int>& oldId2NewId) {
  assert(decisionLevel() == 0);  // so we don't need to update the pointer of Reason<CRef>
  if (options.verbosity > 0) puts("c GARBAGE COLLECT");
  for (Lit l = -n; l <= n; ++l) {
    for (int i = 0; i < (int)adj[l].size(); ++i) {
      if (oldId2NewId[adj[l][i].iID] == -1) aux::swapErase(adj[l], i--);
      else adj[l][i].iID = oldId2NewId[adj[l][i].iID];
    }
  }

  ca.wasted = 0;
  ca.at = 0;
  std::unordered_map<uint32_t, CRef> crefmap;
  for (int i = 1; i < (int)constraints.size(); ++i) assert(constraints[i - 1].ofs < constraints[i].ofs);
  
  for (auto& cr : constraints) {
    uint32_t offset = cr.ofs;
    int memSize = ca[cr].getMemSize();
    memmove(ca.memory + ca.at, ca.memory + cr.ofs, sizeof(uint32_t) * memSize);
    cr.ofs = ca.at;
    ca.at += memSize;
    crefmap[offset] = cr;
  }
#define update_ptr(cr) cr = crefmap[cr.ofs];
  for (auto& ext : external) update_ptr(ext.second);
#undef update_ptr
}

// We assume in the garbage collection method that reduceDB() is the
// only place where constraints are removed from memory.
void Solver::reduceDB() {
  assert(decisionLevel() == 0);
  assert(iID == slackMM.size());
  assert(iID == constraints.size());

  std::vector<std::pair<CRef, uint32_t>> learnts;
  learnts.reserve(constraints.size() / 2);

  size_t totalLearnts = 0;
  size_t promisingLearnts = 0;
  std::vector<bool> ctrIsRemoved(constraints.size(), false);
  
  for (uint i = 0; i < constraints.size(); ++i) {
    Constr& C = ca[constraints[i]];
    
    ConstraintType type = C.getType();
    if (type == ConstraintType::EXTERNAL) continue;
    if (type == ConstraintType::AUXILIARY) {ctrIsRemoved[i] = true; continue;}
    
    Val eval = -C.degree;
    const int Csize = (int)C.size();
    
    for (int j = 0; j < Csize && eval < 0; ++j)
      if (isUnit(Level, C.lit(j))) eval += C.coef(j);
    if (eval >= 0)
      ctrIsRemoved[i] = true;  // remove constraints satisfied at root
    else if (C.getType() == ConstraintType::LEARNT) {
      int lbd = C.lbd();
      if (Csize > 2 && lbd > 2) learnts.push_back({constraints[i], i});  // Keep all binary clauses and short LBDs
      if (Csize <= 2 || lbd <= 3) ++promisingLearnts;
      ++totalLearnts;
    }
  }

  if (promisingLearnts > totalLearnts / 2)
    nconfl_to_reduce += 10 * options.incReduceDB;
  else
    nconfl_to_reduce += options.incReduceDB;
  std::sort(learnts.begin(), learnts.end(), [&](std::pair<CRef, uint32_t>& x, std::pair<CRef, uint32_t>& y) {
    return ca[x.first].lbd() > ca[y.first].lbd() || (ca[x.first].lbd() == ca[y.first].lbd() && ca[x.first].act < ca[y.first].act);
  });
  size_t numDelete = std::min(totalLearnts / 2, learnts.size());
  for (size_t i = 0; i < numDelete; ++i) ctrIsRemoved[learnts[i].second] = true;

  size_t i = 0;
  size_t j = 0;
  std::vector<int> oldId2NewId(constraints.size(), -1);
  for (; i < constraints.size(); ++i) {
    if (!ctrIsRemoved[i]) {
      oldId2NewId[i] = j;
      slackMM[j]  = slackMM[i];
      constraints[j++] = constraints[i];
    }
  }
  constraints.resize(j);
  slackMM.resize(j);
  iID = j;
  
  garbage_collect(oldId2NewId);
    
}

// ---------------------------------------------------------------------
// Solving

double Solver::luby(double y, int i) {
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

Val Solver::lhs(Constr& C, const std::vector<bool>& sol) {
  Val result = 0;
  for (size_t j = 0; j < C.size(); ++j) {
    Lit l = C.lit(j);
    result += ((l > 0) == sol[std::abs(l)]) * C.coef(j);
  }
  return result;
}
bool Solver::checksol(const std::vector<bool>& sol) {
  for (auto& cr : constraints) {
    Constr& C = ca[cr];
    if (C.getType() == ConstraintType::FORMULA && lhs(C, sol) < C.degree) return false;
  }
  return true;
}

Lit Solver::pickBranchLit() {
  Var next = 0;
  // Activity based decision:
  while (next == 0 || !isUnknown(Pos, next)) {
    if (order_heap.empty())
      return 0;
    else
      next = order_heap.removeMax();
  }
  assert(phase[0] == 0);
  return phase[next];
}

/**
 * @return:
 *  UNSAT if root inconsistency detected
 *  SAT if satisfying assignment found
 *  INCONSISTENT if no solution extending assumptions exists
 *  INTERRUPTED if interrupted by external signal
 *  INRPOCESSED if solver just finished a cleanup phase
 *  RESTARTED if solver just restarted
 * @param assumptions: set of assumptions
 * @param core: if INCONSISTENT, implied constraint falsified by assumptions, otherwise untouched
 *  if core is the empty constraint, at least one assumption is falsified at root
 * @param solution: if SAT, full variable assignment satisfying all constraints, otherwise untouched
 */
// TODO: use a coroutine / yield instead of a SolveState return value
SolveState Solver::solve(const IntSet& assumptions, intConstr& core, std::vector<bool>& solution) {
  assert(iID == slackMM.size());
  assert(iID == constraints.size());
  backjumpTo(0);  // ensures assumptions are reset
  std::vector<int> assumptions_lim = {0};
  assumptions_lim.reserve((int)assumptions.size() + 1);
  bool allClear = false;
  while (true) {
    if (asynch_interrupt) return SolveState::INTERRUPTED;
    assert(conflConstraint.isReset());
    if (processLearnedStack() == CRef_Unsat) return SolveState::UNSAT;
    allClear = runPropagation();
    if (!allClear) {
      assert(!conflConstraint.isReset());
      vDecayActivity();
      cDecayActivity();
      stats.NCONFL++;
      nconfl_to_restart--;
      if (stats.NCONFL % 1000 == 0 && options.verbosity > 0) {
        printf("c #conflicts: %10lld | #Constraints: %10lld\n", stats.NCONFL, (long long)constraints.size());
        if (options.verbosity > 2) {
          // memory usage
          std::cout << "c total constraint space: " << ca.cap * 4 / 1024. / 1024. << "MB" << std::endl;
          std::cout << "c total #watches: ";
          long long cnt = 0;
          for (Lit l = -n; l <= n; l++) cnt += (long long)adj[l].size();
          std::cout << cnt << std::endl;
        }
      }
      if (decisionLevel() == 0) {
        if (logger) {
          conflConstraint.logInconsistency(Level, Pos, stats);
          conflConstraint.reset();
        }
        return SolveState::UNSAT;
      } else if (decisionLevel() >= (int)assumptions_lim.size()) {
        if (!analyze()) return SolveState::INTERRUPTED;
        assert(conflConstraint.getDegree() > 0);
        assert(conflConstraint.getDegree() < INF);
        assert(conflConstraint.isSaturated());
        learnConstraint(conflConstraint);
        conflConstraint.reset();
      } else {
        if (!extractCore(assumptions, core)) return SolveState::INTERRUPTED;
        return SolveState::INCONSISTENT;
      }
    } else {
      if (nconfl_to_restart <= 0) {
        backjumpTo(0);
        if (stats.NCONFL >= (stats.NCLEANUP + 1) * nconfl_to_reduce) {
          ++stats.NCLEANUP;
          if (options.verbosity > 0) puts("c INPROCESSING");
          reduceDB();
          while (stats.NCONFL >= stats.NCLEANUP * nconfl_to_reduce) nconfl_to_reduce += options.incReduceDB;
          return SolveState::INPROCESSED;
        }
        double rest_base = luby(options.rinc, ++stats.NRESTARTS);
        nconfl_to_restart = (long long)rest_base * options.rfirst;
        return SolveState::RESTARTED;
      }
      Lit next = 0;
      if ((int)assumptions_lim.size() > decisionLevel() + 1) assumptions_lim.resize(decisionLevel() + 1);
      if (assumptions_lim.back() < (int)assumptions.size()) {
        for (int i = (decisionLevel() == 0 ? 0 : trail_lim.back()); i < (int)trail.size(); ++i) {
          Lit l = trail[i];
          if (assumptions.has(-l)) {  // found conflicting assumption
            if (isUnit(Level, l))
              backjumpTo(0), core.reset();  // negated assumption is unit
            else {
              ca[Reason[std::abs(l)]].toConstraint(conflConstraint);
              if (!extractCore(assumptions, core, -l)) return SolveState::INTERRUPTED;
            }
            return SolveState::INCONSISTENT;
          }
        }
      }
      while (assumptions_lim.back() < (int)assumptions.size()) {
        assert(decisionLevel() == (int)assumptions_lim.size() - 1);
        Lit l_assump = assumptions.keys[assumptions_lim.back()];
        assert(!isFalse(Level, l_assump));  // otherwise above check should have caught this
        if (isTrue(Level, l_assump)) {      // assumption already propagated
          ++assumptions_lim.back();
        } else {  // unassigned assumption
          next = l_assump;
          assumptions_lim.push_back(assumptions_lim.back() + 1);
          break;
        }
      }
      if (next == 0) next = pickBranchLit();
      if (next == 0) {
        assert(order_heap.empty());
        assert((int)trail.size() == n);
        solution.clear();
        solution.resize(n + 1);
        solution[0] = false;
        for (Var v = 1; v <= n; ++v) solution[v] = isTrue(Level, v);
        backjumpTo(0);
        assert(checksol(solution));
        return SolveState::SAT;
      }
      if (timeout()) return SolveState::INTERRUPTED;
      decide(next);
    }
  }
}

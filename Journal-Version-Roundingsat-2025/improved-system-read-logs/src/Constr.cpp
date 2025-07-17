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

#include "Constr.hpp"

#include "ConstrExpPool.hpp"
#include "Solver.hpp"

namespace rs {

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wbitfield-constant-conversion"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Woverflow"
#endif
static_assert((unsigned int)Origin::NUM_ORIGINS - 1 < ((Constr::Header){0, (unsigned)-1, 0, 0, 0}).origin + 1, "Too many Origins to fit into the size of the Constr.header.origin field.");
#ifdef __clang__
#pragma clang diagnostic pop
#else
#pragma GCC diagnostic pop
#endif

void Clause::initializeWatches(CRef cr, Solver& solver) {
  solver.slackMCoefV.emplace_back(SlackMC());
  auto& Level = solver.Level;
  auto& adj = solver.adj;

  unsigned int length = size();
  assert(length >= 1);
  if (length == 1) {
    assert(solver.decisionLevel() == 0);
    assert(isCorrectlyPropagating(solver, 0));
    solver.propagate(data[0], cr);
    return;
  }

  unsigned int watch = 0;
  for (unsigned int i = 0; i < length && watch <= 1; ++i) {
    Lit l = data[i];
    if (!isFalse(Level, l)) {
      data[i] = data[watch];
      data[watch++] = l;
    }
  }
  assert(watch >= 1);  // we found enough watches to satisfy the constraint
  assert((watch == 1) == isFalse(Level, data[1]));
  if (watch == 1) {
    assert(!isFalse(Level, data[0]));
    if (!isTrue(Level, data[0])) {
      assert(isCorrectlyPropagating(solver, 0));
      solver.propagate(data[0], cr);
    }
    for (unsigned int i = 2; i < length; ++i) {  // ensure last watch is last falsified literal
      Lit l = data[i];
      assert(isFalse(Level, l));
      if (Level[-l] > Level[-data[1]]) {
        data[i] = data[1];
        data[1] = l;
      }
    }
  }
  for (unsigned int i = 0; i < 2; ++i) {
    adj[data[i]].emplace_back(solver.iID, data[1 - i] - INF);  // add blocked literal
  }
}

WatchStatus Clause::checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, const int iID) {
  ++stats.NLOADCLAUSES;
  auto& Level = solver.Level;
  auto& adj = solver.adj;

  assert(idx < 0);
  assert(p == data[0] || p == data[1]);
  assert(size() > 1);
  int widx = 0;
  Lit watch = data[0];
  Lit otherwatch = data[1];
  if (p == data[1]) {
    widx = 1;
    watch = data[1];
    otherwatch = data[0];
  }
  assert(p == watch);
  assert(p != otherwatch);
  if (isTrue(Level, otherwatch)) {
    idx = otherwatch - INF;         // set new blocked literal
    return WatchStatus::KEEPWATCH;  // constraint is satisfied
  }

  const unsigned int length = size();
  for (unsigned int i = 2; i < length; ++i) {
    Lit l = data[i];
    if (!isFalse(Level, l)) {
      unsigned int mid = i / 2 + 1;
      data[i] = data[mid];
      data[mid] = watch;
      data[widx] = l;
      adj[l].emplace_back(iID, otherwatch - INF);
      stats.NWATCHCHECKS += i - 1;
      return WatchStatus::DROPWATCH;
    }
  }
  stats.NWATCHCHECKS += length - 2;

  assert(isFalse(Level, watch));
  for (unsigned int i = 2; i < length; ++i) assert(isFalse(Level, data[i]));
  if (isFalse(Level, otherwatch)) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  } else {
    assert(!isTrue(Level, otherwatch));
    ++stats.NPROPCLAUSE;
    assert(isCorrectlyPropagating(solver, 1 - widx));
    solver.propagate(otherwatch, cr);
  }
  ++stats.NPROPCHECKS;
  return WatchStatus::KEEPWATCH;
}

void Clause::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(*this, l, actSet, solver.getLevel(), solver.getPos());
}

CeSuper Clause::toExpanded(ConstrExpPools& cePools) const {
  Ce32 result = cePools.take32();
  result->addRhs(1);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(1, data[i]);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

bool Clause::isSatisfiedAtRoot(const IntVecIt& level) const {
  for (int i = 0; i < (int)size(); ++i) {
    if (isUnit(level, data[i])) return true;
  }
  return false;
}

void Cardinality::initializeWatches(CRef cr, Solver& solver) {
  solver.slackMCoefV.emplace_back(SlackMC());
  auto& Level = solver.Level;
  [[maybe_unused]] auto& Pos = solver.Pos;
  auto& adj = solver.adj;

  unsigned int length = size();
  if (degr >= length) {
    assert(solver.decisionLevel() == 0);
    for (unsigned int i = 0; i < length; ++i) {
      assert(isUnknown(Pos, data[i]));
      assert(isCorrectlyPropagating(solver, i));
      solver.propagate(data[i], cr);
    }
    return;
  }

  unsigned int watch = 0;
  for (unsigned int i = 0; i < length && watch <= degr; ++i) {
    Lit l = data[i];
    if (!isFalse(Level, l)) {
      data[i] = data[watch];
      data[watch++] = l;
    }
  }
  assert(watch >= degr);  // we found enough watches to satisfy the constraint
  if (isFalse(Level, data[degr])) {
    for (unsigned int i = 0; i < degr; ++i) {
      assert(!isFalse(Level, data[i]));
      if (!isTrue(Level, data[i])) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i], cr);
      }
    }
    for (unsigned int i = degr + 1; i < size(); ++i) {  // ensure last watch is last falsified literal
      Lit l = data[i];
      assert(isFalse(Level, l));
      if (Level[-l] > Level[-data[degr]]) {
        data[i] = data[degr];
        data[degr] = l;
      }
    }
  }
  nextWatchIdx = degr + 1;
  for (unsigned int i = 0; i <= degr; ++i) adj[data[i]].emplace_back(solver.iID, i);   // add watch index
}

WatchStatus Cardinality::checkForPropagation(CRef cr, int& idx, [[maybe_unused]] Lit p, Solver& solver, const int iID) {
  ++stats.NLOADCARDS;
  auto& Level = solver.Level;
  auto& adj = solver.adj;

  assert(idx < INF);
  assert(data[idx] == p);
  const unsigned int length = size();
  if (!options.propIdx || ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS;
    nextWatchIdx = degr + 1;
  }
  assert(nextWatchIdx > degr);
  stats.NWATCHCHECKS -= nextWatchIdx;
  for (; nextWatchIdx < length; ++nextWatchIdx) {
    Lit l = data[nextWatchIdx];
    if (!isFalse(Level, l)) {
      unsigned int mid = (nextWatchIdx + degr + 1) / 2;
      assert(mid <= nextWatchIdx);
      assert(mid > degr);
      data[nextWatchIdx] = data[mid];
      data[mid] = data[idx];
      data[idx] = l;
      adj[l].emplace_back(iID, idx);
      stats.NWATCHCHECKS += nextWatchIdx + 1;
      return WatchStatus::DROPWATCH;
    }
  }
  stats.NWATCHCHECKS += nextWatchIdx;
  assert(isFalse(Level, data[idx]));
  for (unsigned int i = degr + 1; i < length; ++i) assert(isFalse(Level, data[i]));
  for (int i = 0; i <= (int)degr; ++i)
    if (i != idx && isFalse(Level, data[i])) {
      assert(isCorrectlyConflicting(solver));
      return WatchStatus::CONFLICTING;
    }
  for (int i = 0; i <= (int)degr; ++i) {
    Lit l = data[i];
    if (i != idx && !isTrue(Level, l)) {
      ++stats.NPROPCARD;
      assert(isCorrectlyPropagating(solver, i));
      solver.propagate(l, cr);
    }
  }
  stats.NPROPCHECKS += degr + 1;
  return WatchStatus::KEEPWATCH;
}

void Cardinality::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(*this, l, actSet, solver.getLevel(), solver.getPos());
}

CeSuper Cardinality::toExpanded(ConstrExpPools& cePools) const {
  Ce32 result = cePools.take32();
  result->addRhs(degr);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(1, data[i]);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

bool Cardinality::isSatisfiedAtRoot(const IntVecIt& level) const {
  int eval = -degr;
  for (int i = 0; i < (int)size() && eval < 0; ++i)
    if (isUnit(level, data[i])) ++eval;
  return eval >= 0;
}

template <typename CF, typename DG>
void Counting<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  DG slack = -degr;
  unsigned int length = size();
  for (unsigned int i = 0; i < length; ++i) {
    Lit l = data[i].l; CF c = data[i].c;
    assert(c <= limit64);
    adj[l].emplace_back(solver.iID, i + INF, c);
    if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) slack += c;
  }

  assert(slack >= 0);
  const CF lrgstCf = data[0].c;
  if (slack < lrgstCf) {  // propagate
    unsigned int i = 0;
    for (; i < length && data[i].c > slack; ++i)
      if (isUnknown(Pos, data[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i].l, cr);
      }
    nextWatchIdx = i;
  }
  solver.slackMCoefV.emplace_back(0, 1, slack-lrgstCf);
  assert(hasCorrectSlack(solver, solver.iID));

#ifndef NDEBUG
  SlackMC& smc = solver.slackMCoefV[solver.iID];
  assert(smc.isVal);
  assert(static_cast<DG>(smc.slackMC) == slack-data[0].c);
#endif
}

template <typename CF, typename DG>
WatchStatus Counting<CF, DG>::checkForPropagation(CRef cr, [[maybe_unused]] int& idx, Lit p, Solver& solver, const int iID) {
  _unused(p);
  ++stats.NLOADPBCOUNTING;
  auto& Pos = solver.Pos;

  assert(idx >= INF);
  assert(data[idx - INF].l == p);
  const unsigned int length = size();
  const CF& lrgstCf = data[0].c;

  SlackMC& smc = solver.slackMCoefV[iID];
  assert(smc.isVal);
  assert(smc.slackMC < 0);
  DG slack = static_cast<DG>(smc.slackMC + lrgstCf);

  assert(hasCorrectSlack(solver, iID));

  if (slack < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  assert(slack < lrgstCf);
  if (!options.propIdx || ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS;
    nextWatchIdx = 0;
  }
  stats.NPROPCHECKS -= nextWatchIdx;
  for (; nextWatchIdx < length && data[nextWatchIdx].c > slack; ++nextWatchIdx) {
    const Lit l = data[nextWatchIdx].l;
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (degr == 1);
      stats.NPROPCARD += (degr != 1 && lrgstCf == 1);
      ++stats.NPROPCOUNTING;
      assert(isCorrectlyPropagating(solver, nextWatchIdx));
      solver.propagate(l, cr);
    }
  }
  stats.NPROPCHECKS += nextWatchIdx;
  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void Counting<CF, DG>::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(expandTo(solver.cePools), l, actSet, solver.getLevel(), solver.getPos());
}

template <typename CF, typename DG>
CePtr<ConstrExp<CF, DG>> Counting<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<ConstrExp<CF, DG>> result = cePools.take<CF, DG>();
  result->addRhs(degr);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(data[i].c, data[i].l);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

template <typename CF, typename DG>
CeSuper Counting<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool Counting<CF, DG>::isSatisfiedAtRoot(const IntVecIt& level) const {
  DG eval = -degr;
  for (int i = 0; i < (int)size() && eval < 0; ++i)
    if (isUnit(level, data[i].l)) eval += data[i].c;
  return eval >= 0;
}

template <typename CF, typename DG>
void Watched<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  DG watchslack = -degr;
  unsigned int length = size();
  const CF lrgstCf = aux::abs(data[0].c);
  for (unsigned int i = 0; i < length && watchslack < lrgstCf; ++i) {
    Lit l = data[i].l;
    if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) {
      assert(data[i].c > 0);
      watchslack += data[i].c;
      assert(data[i].c <= limit64);
      data[i].c = -data[i].c;
      adj[l].emplace_back(solver.iID, i + INF, data[i].c);
    }
  }
  assert(watchslack >= 0);
  if (watchslack < lrgstCf) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(length);
    for (unsigned int i = 0; i < length; ++i)
      if (isFalse(Level, data[i].l) && Pos[toVar(data[i].l)] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(),
              [&](unsigned int i1, unsigned int i2) { return Pos[toVar(data[i1].l)] > Pos[toVar(data[i2].l)]; });
    DG diff = lrgstCf - watchslack;
    for (unsigned int i : falsifiedIdcs) {
      assert(data[i].c > 0);
      diff -= data[i].c;
      assert(data[i].c <= limit64);
      data[i].c = -data[i].c;
      adj[data[i].l].emplace_back(solver.iID, i + INF, data[i].c);
      if (diff <= 0) break;
    }
    // perform initial propagation
    unsigned int i;
    for (i = 0; i < length && aux::abs(data[i].c) > watchslack; ++i) {
      if (isUnknown(Pos, data[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(data[i].l, cr);
      }
    }
    nextWatchIdx = i;
  }

  solver.slackMCoefV.emplace_back(0, 1, watchslack-lrgstCf);
  assert(hasCorrectSlack(solver, solver.iID));
}

  // circular search, lazy version
template <typename CF, typename DG>
WatchStatus Watched<CF, DG>::checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, const int iID) {
  _unused(p);
  ++stats.NLOADPBWATCHED;
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;

  assert(idx >= INF);
  assert(data[idx - INF].l == p);
  const unsigned int length = size();
  const CF lrgstCf = aux::abs(data[0].c);
  CF& c = data[idx - INF].c;

  SlackMC& smc = solver.slackMCoefV[iID];
  assert(smc.isVal);

  DG snfMC = static_cast<DG>(smc.slackMC);
  assert(c < 0);

  if (!options.propSup || snfMC - c >= 0) {  // look for new watches if previously, slack was at least lrgstCf
    unsigned int start_widx = nextWatchIdx;
    stats.NWATCHCHECKS -= nextWatchIdx;
    for (; nextWatchIdx < length && snfMC < 0; ++nextWatchIdx) {
      const CF& cf = data[nextWatchIdx].c;
      const Lit l = data[nextWatchIdx].l;
      if (cf > 0 && !isFalse(Level, l)) {
        snfMC += cf;
        data[nextWatchIdx].c = -cf;
        adj[l].emplace_back(iID, nextWatchIdx + INF, cf);
      }
    }  // NOTE: first innermost loop of RoundingSat
    stats.NWATCHCHECKS += nextWatchIdx;

    if (snfMC < 0 && ntrailpops < stats.NTRAILPOPS) {
      ntrailpops = stats.NTRAILPOPS;
      nextWatchIdx = 0;
      for (; nextWatchIdx < start_widx && snfMC < 0; ++nextWatchIdx) {
        const CF& cf = data[nextWatchIdx].c;
        const Lit l = data[nextWatchIdx].l;
        if (cf > 0 && !isFalse(Level, l)) {
          snfMC += cf;
          data[nextWatchIdx].c = -cf;
          adj[l].emplace_back(iID, nextWatchIdx + INF, cf);
        }
      }  // NOTE: first innermost loop of RoundingSat
      stats.NWATCHCHECKS += nextWatchIdx;
    }

    smc.slackMC = snfMC;
    if (snfMC < 0) {
      nextWatchIdx = 0;
    }
    else {
      c = -c;
      return WatchStatus::DROPWATCH;
    }
  }  // else we did not find enough watches last time, so we can skip looking for them now

  assert(snfMC < 0);
  assert(hasCorrectSlack(solver, iID));

  DG watchslack = snfMC + lrgstCf;
  if (watchslack < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  if (ntrailpops < stats.NTRAILPOPS || !options.propIdx ) {
    ntrailpops = stats.NTRAILPOPS;
    nextWatchIdx = 0;
  }

  // keep the watch, check for propagation
  stats.NPROPCHECKS -= nextWatchIdx;
  for (; nextWatchIdx < length && aux::abs(data[nextWatchIdx].c) > watchslack; ++nextWatchIdx) {
    const Lit l = data[nextWatchIdx].l;
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (degr == 1);
      stats.NPROPCARD += (degr != 1 && lrgstCf == 1);
      ++stats.NPROPWATCH;
      assert(isCorrectlyPropagating(solver, nextWatchIdx));
      solver.propagate(l, cr);
    }  // NOTE: second innermost loop of RoundingSat
  }
  stats.NPROPCHECKS += nextWatchIdx;
  return WatchStatus::KEEPWATCH;
}



template <typename CF, typename DG>
void Watched<CF, DG>::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(expandTo(solver.cePools), l, actSet, solver.getLevel(), solver.getPos());
}

template <typename CF, typename DG>
CePtr<ConstrExp<CF, DG>> Watched<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<ConstrExp<CF, DG>> result = cePools.take<CF, DG>();
  result->addRhs(degr);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(aux::abs(data[i].c), data[i].l);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

template <typename CF, typename DG>
CeSuper Watched<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool Watched<CF, DG>::isSatisfiedAtRoot(const IntVecIt& level) const {
  DG eval = -degr;
  for (int i = 0; i < (int)size() && eval < 0; ++i)
    if (isUnit(level, data[i].l)) eval += aux::abs(data[i].c);
  return eval >= 0;
}

template <typename CF, typename DG>
long long CountingSafe<CF, DG>::getBigCoefPtr(const CF& c, unsigned int& csize) const {
  assert(c > 0);
  long long x;
  if (c <= limit64) {  // it fits in 61 bits
    csize = 0;
    x = static_cast<long long>(c);
  }
  else {
    x = reinterpret_cast<long long>(&c);
    assert(x <= limit64);
    assert(*(reinterpret_cast<CF*>(x)) == c);
  }
  return x;
}


template <typename CF, typename DG>
long long CountingSafe<CF, DG>::getNewCoefPtr(const int idx) {
  assert(idx >= 0 && idx < (int)size());
  assert(terms[idx].c > 0);
  assert(terms[idx].c > limit64);
  long long x = reinterpret_cast<long long>(&terms[idx].c);
  assert(abs(x) < limit64);
  return x;
}

template <typename CF, typename DG>
void CountingSafe<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;
  int nBigInts = 0;
  unsigned int csize = 0, cfSize = sizeof(CF);
  unsigned int cfSign = ((cfSize == 8)? SIGN_PTR_64 : ((cfSize == 16)? SIGN_PTR_128 : SIGN_PTR_BIGINT));
  DG slk = -*degr;
  unsigned int length = size();
  for (unsigned int i = 0; i < length; ++i) {
    Lit l = terms[i].l;
    csize = cfSign;
    long long x = getBigCoefPtr(terms[i].c, csize);
    assert(x > 0);
    nBigInts += (csize != 0);
    adj[l].emplace_back(solver.iID, i + INF, csize, x);
    if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) slk += terms[i].c;
  }
  //std::cout << "c id " << id << ", nBigInts = " << nBigInts << " ( " << (double)nBigInts/length*100 << " ) " << std::endl;

  assert(slk >= 0);
  if (slk < terms[0].c) {  // propagate
    unsigned int i;
    for (i = 0; i < length && terms[i].c > slk; ++i) {
      Lit l = terms[i].l;
      if (isUnknown(Pos, l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(l, cr);
      }
    }
    nextWatchIdx = i;
  }

  DG* p = new DG(slk-terms[0].c);
  solver.slackMCoefV.emplace_back(0, p);
  assert(hasCorrectSlack(solver, solver.iID));
}

template <typename CF, typename DG>
WatchStatus CountingSafe<CF, DG>::checkForPropagation(CRef cr, [[maybe_unused]] int& idx, [[maybe_unused]] Lit p, Solver& solver, const int iID) {
  ++stats.NLOADPBCOUNTING;
  auto& Pos = solver.Pos;

  assert(idx >= INF);
  assert(terms[idx - INF].l == p);
  const unsigned int length = size();
  const CF& lrgstCf = terms[0].c;

  assert(hasCorrectSlack(solver, iID));

  SlackMC& smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = smc.dereference<DG>();
  DG slk = v + lrgstCf;

  if (slk < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  assert(slk < lrgstCf);
  if (!options.propIdx || ntrailpops < stats.NTRAILPOPS) {
    ntrailpops = stats.NTRAILPOPS;
    nextWatchIdx = 0;
  }
  stats.NPROPCHECKS -= nextWatchIdx;
  for (; nextWatchIdx < length && terms[nextWatchIdx].c > slk; ++nextWatchIdx) {
    const Lit l = terms[nextWatchIdx].l;
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (*degr == 1);
      stats.NPROPCARD += (*degr != 1 && lrgstCf == 1);
      ++stats.NPROPCOUNTING;
      assert(isCorrectlyPropagating(solver, nextWatchIdx));
      solver.propagate(l, cr);
    }
  }
  stats.NPROPCHECKS += nextWatchIdx;

  return WatchStatus::KEEPWATCH;
}

template <typename CF, typename DG>
void CountingSafe<CF, DG>::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(expandTo(solver.cePools), l, actSet, solver.getLevel(), solver.getPos());
}

template <typename CF, typename DG>
CePtr<ConstrExp<CF, DG>> CountingSafe<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<ConstrExp<CF, DG>> result = cePools.take<CF, DG>();
  result->addRhs(*degr);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(terms[i].c, terms[i].l);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

template <typename CF, typename DG>
CeSuper CountingSafe<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool CountingSafe<CF, DG>::isSatisfiedAtRoot(const IntVecIt& level) const {
  DG eval = -*degr;
  for (int i = 0; i < (int)size() && eval < 0; ++i)
    if (isUnit(level, terms[i].l)) eval += terms[i].c;
  return eval >= 0;
}

template <typename CF, typename DG>
long long WatchedSafe<CF, DG>::getBigCoefPtr(const CF& c, unsigned int& csize) const {
  assert(c > 0);
  long long x;
  if (c <= limit64) {  // it fits in 61 bits
    csize = 0;
    x = static_cast<long long>(c);
  }
  else {
    x = reinterpret_cast<long long>(&c);
    assert(x <= limit64);
    assert(*(reinterpret_cast<CF*>(x)) == c);
  }
  return -x;
}

template <typename CF, typename DG>
long long WatchedSafe<CF, DG>::getNewCoefPtr(const int idx) {
  assert(idx >= 0 && idx < (int)size());
  assert(terms[idx].c < 0);
  assert(aux::abs(terms[idx].c) > limit64);
  long long x = reinterpret_cast<long long>(&terms[idx].c);
  assert(abs(x) < limit64);
  return -x;
}

template <typename CF, typename DG>
void WatchedSafe<CF, DG>::initializeWatches(CRef cr, Solver& solver) {
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;
  auto& qhead = solver.qhead;

  int nBigInts = 0;
  unsigned int csize = 0, cfSize = sizeof(CF);
  unsigned int cfSign = ((cfSize == 8)? SIGN_PTR_64 : ((cfSize == 16)? SIGN_PTR_128 : SIGN_PTR_BIGINT));
  DG wslk = -*degr;
  unsigned int length = size();
  const CF lrgstCf = aux::abs(terms[0].c);
  for (unsigned int i = 0; i < length && wslk < lrgstCf; ++i) {
    Lit l = terms[i].l;
    if (!isFalse(Level, l) || Pos[toVar(l)] >= qhead) {
      assert(terms[i].c > 0);
      wslk += terms[i].c;
      csize = cfSign;
      long long x = getBigCoefPtr(terms[i].c, csize);
      assert(x < 0);
      nBigInts += (csize != 0);

      terms[i].c = -terms[i].c;
      adj[l].emplace_back(solver.iID, i + INF, csize, x);
    }
  }
  assert(wslk >= 0);
  if (wslk < lrgstCf) {
    // set sufficient falsified watches
    std::vector<unsigned int> falsifiedIdcs;
    falsifiedIdcs.reserve(length);
    for (unsigned int i = 0; i < length; ++i)
      if (isFalse(Level, terms[i].l) && Pos[toVar(terms[i].l)] < qhead) falsifiedIdcs.push_back(i);
    std::sort(falsifiedIdcs.begin(), falsifiedIdcs.end(),
              [&](unsigned int i1, unsigned int i2) { return Pos[toVar(terms[i1].l)] > Pos[toVar(terms[i2].l)]; });
    DG diff = lrgstCf - wslk;
    for (unsigned int i : falsifiedIdcs) {
      assert(terms[i].c > 0);
      diff -= terms[i].c;

      csize = cfSign;
      long long x = getBigCoefPtr(terms[i].c, csize);
      assert(x < 0);
      nBigInts += (csize != 0);

      terms[i].c = -terms[i].c;
      adj[terms[i].l].emplace_back(solver.iID, i + INF, csize, x);

      if (diff <= 0) break;
    }
    // perform initial propagation
    unsigned int i;
    for (i = 0; i < length && aux::abs(terms[i].c) > wslk; ++i)
      if (isUnknown(Pos, terms[i].l)) {
        assert(isCorrectlyPropagating(solver, i));
        solver.propagate(terms[i].l, cr);
      }
    nextWatchIdx = i;
  }
  //std::cout << "c id " << id << ", nBigInts = " << nBigInts << " ( " << (double)nBigInts/length*100 << " ) " << std::endl;

  DG* p = new DG(wslk-lrgstCf);
  solver.slackMCoefV.emplace_back(0, p);
  assert(hasCorrectSlack(solver, solver.iID));
}

  // circular search , lazy version
template <typename CF, typename DG>
WatchStatus WatchedSafe<CF, DG>::checkForPropagation(CRef cr, int& idx, Lit p, Solver& solver, const int iID) {
  _unused(p);
  ++stats.NLOADPBWATCHED;
  auto& Level = solver.Level;
  auto& Pos = solver.Pos;
  auto& adj = solver.adj;

  assert(idx >= INF);
  assert(terms[idx - INF].l == p);
  const unsigned int length = size();
  const CF lrgstCf = aux::abs(terms[0].c);
  CF& c = terms[idx - INF].c;

  SlackMC& smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& snfMC = smc.dereference<DG>();
  assert(c < 0);

  if (!options.propSup || snfMC - c >= 0) {  // look for new watches if previously, slack was at least lrgstCf
    unsigned int start_widx = nextWatchIdx;
    stats.NWATCHCHECKS -= nextWatchIdx;
    unsigned int csize = 0, cfSize = sizeof(CF);
    unsigned int cfSign = ((cfSize == 8)? SIGN_PTR_64 : ((cfSize == 16)? SIGN_PTR_128 : SIGN_PTR_BIGINT));
    for (; nextWatchIdx < length && snfMC < 0; ++nextWatchIdx) {
      const CF& cf = terms[nextWatchIdx].c;
      const Lit l = terms[nextWatchIdx].l;
      if (cf > 0 && !isFalse(Level, l)) {
        snfMC += cf;
        csize = cfSign;
        long long x = getBigCoefPtr(cf, csize);
        assert(x < 0);
        terms[nextWatchIdx].c = -cf;
        adj[l].emplace_back(iID, nextWatchIdx + INF, csize, x);
      }
    }  // NOTE: first innermost loop of RoundingSat
    stats.NWATCHCHECKS += nextWatchIdx;

    if (snfMC < 0 && ntrailpops < stats.NTRAILPOPS) {
      ntrailpops = stats.NTRAILPOPS;
      nextWatchIdx = 0;

      for (; nextWatchIdx < start_widx && snfMC < 0; ++nextWatchIdx) {
        const CF& cf = terms[nextWatchIdx].c;
        const Lit l = terms[nextWatchIdx].l;
        if (cf > 0 && !isFalse(Level, l)) {
          snfMC += cf;
          csize = cfSign;
          long long x = getBigCoefPtr(cf, csize);
          assert(x < 0);
          terms[nextWatchIdx].c = -cf;
          adj[l].emplace_back(iID, nextWatchIdx + INF, csize, x);
        }
      }  // NOTE: first innermost loop of RoundingSat
      stats.NWATCHCHECKS += nextWatchIdx;

    }

    if (snfMC < 0) {
      nextWatchIdx = 0;
    }
    else {
      c = -c;
      return WatchStatus::DROPWATCH;
    }
  }  // else we did not find enough watches last time, so we can skip looking for them now
  assert(snfMC < 0);
  assert(hasCorrectSlack(solver, iID));

  DG wslk = snfMC + lrgstCf;
  if (wslk < 0) {
    assert(isCorrectlyConflicting(solver));
    return WatchStatus::CONFLICTING;
  }
  if (ntrailpops < stats.NTRAILPOPS || !options.propIdx) {
    ntrailpops = stats.NTRAILPOPS;
    nextWatchIdx = 0;
  }

  // keep the watch, check for propagation
  stats.NPROPCHECKS -= nextWatchIdx;
  for (; nextWatchIdx < length && aux::abs(terms[nextWatchIdx].c) > wslk; ++nextWatchIdx) {
    const Lit l = terms[nextWatchIdx].l;
    if (isUnknown(Pos, l)) {
      stats.NPROPCLAUSE += (*degr == 1);
      stats.NPROPCARD += (*degr != 1 && lrgstCf == 1);
      ++stats.NPROPWATCH;
      assert(isCorrectlyPropagating(solver, nextWatchIdx));
      solver.propagate(l, cr);
    }  // NOTE: second innermost loop of RoundingSat
  }
  stats.NPROPCHECKS += nextWatchIdx;
  return WatchStatus::KEEPWATCH;
}



template <typename CF, typename DG>
void WatchedSafe<CF, DG>::resolveWith(CeSuper confl, Lit l, IntSet* actSet, Solver& solver) {
  confl->resolveWith(expandTo(solver.cePools), l, actSet, solver.getLevel(), solver.getPos());
}

template <typename CF, typename DG>
CePtr<ConstrExp<CF, DG>> WatchedSafe<CF, DG>::expandTo(ConstrExpPools& cePools) const {
  CePtr<ConstrExp<CF, DG>> result = cePools.take<CF, DG>();
  result->addRhs(*degr);
  for (size_t i = 0; i < size(); ++i) {
    result->addLhs(aux::abs(terms[i].c), terms[i].l);
  }
  result->orig = getOrigin();
  if (result->plogger) result->proof.reset(id);
  return result;
}

template <typename CF, typename DG>
CeSuper WatchedSafe<CF, DG>::toExpanded(ConstrExpPools& cePools) const {
  return expandTo(cePools);
}

template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::isSatisfiedAtRoot(const IntVecIt& level) const {
  DG eval = -*degr;
  for (int i = 0; i < (int)size() && eval < 0; ++i)
    if (isUnit(level, terms[i].l)) eval += aux::abs(terms[i].c);
  return eval >= 0;
}

// Added below for quicker proof checking

std::vector<Lit> Clause::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -data[i])) units.push_back(data[i]);
  return units;
}

std::vector<Lit> Cardinality::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -data[i])) units.push_back(data[i]);
  return units;
}

template <typename CF, typename DG>
std::vector<Lit> Counting<CF, DG>::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -data[i].l)) units.push_back(data[i].l);
  return units;
}

template <typename CF, typename DG>
std::vector<Lit> Watched<CF, DG>::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -data[i].l)) units.push_back(data[i].l);
  return units;
}

template <typename CF, typename DG>
std::vector<Lit> CountingSafe<CF, DG>::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -terms[i].l)) units.push_back(terms[i].l);
  return units;
}

template <typename CF, typename DG>
std::vector<Lit> WatchedSafe<CF, DG>::falsifiedUnits(const IntVecIt& level) const {
  std::vector<Lit> units;
  for (int i = 0; i < (int)size(); ++i)
    if (isUnit(level, -terms[i].l)) units.push_back(terms[i].l);
  return units;
}

// Debug method.
bool Constr::isCorrectlyConflicting(const Solver& solver) {
  BigVal slack = -degree();
  for (int i = 0; i < (int)size(); ++i) {
    slack += isFalse(solver.getLevel(), lit(i)) ? 0 : coef(i);
  }
  return slack < 0;
}

// Debug method.
bool Constr::isCorrectlyPropagating(const Solver& solver, int idx) {
  assert(isUnknown(solver.getPos(), lit(idx)));
  BigVal slack = -degree();
  for (int i = 0; i < (int)size(); ++i) {
    slack += isFalse(solver.getLevel(), lit(i)) ? 0 : coef(i);
  }
  return slack < coef(idx);
}

void Constr::print(const Solver& solver) {
  for (size_t i = 0; i < size(); ++i) {
    int pos = solver.getPos()[toVar(lit(i))];
    std::cout << coef(i) << "x" << lit(i)
              << (pos < solver.qhead ? (isTrue(solver.getLevel(), lit(i)) ? "t" : "f") : "u") << (pos == INF ? -1 : pos)
              << " ";
  }
  std::cout << ">= " << degree() << std::endl;
}

// Debug method.
void Cardinality::allLitsPropagated(const Solver& solver, const int iID) {
  auto& Pos = solver.Pos;
  auto& level = solver.getLevel();
  unsigned int nTrue = 0, nUndef = 0;
  for (int i = 0; i < (int)size(); ++i) {
    if (isTrue(level, data[i])) ++nTrue;
    else if (Pos[toVar(data[i])] >= solver.qhead) ++nUndef;
  }
  if (nUndef + nTrue < degr) {
    std::cout << "Cardinality iID " << iID << " is conflicting. nUndef = " << nUndef << ", nTrue = " << nTrue << ", degr = " << degr << std::endl;
    abort();
  }
  else if (nUndef + nTrue == degr and nUndef > 0) {
    std::cout << "Cardinality iID " << iID << " is not completely propagated. nUndef = " << nUndef << ", nTrue = " << nTrue << ", degr = " << degr << std::endl;
    abort();
  }
}

// Debug method.
void Clause::allLitsPropagated(const Solver& solver, const int iID) {
  auto& Pos = solver.Pos;
  auto& level = solver.getLevel();
  unsigned int nTrue = 0, nUndef = 0;
  for (int i = 0; i < (int)size(); ++i) {
    if (isTrue(level, data[i])) ++nTrue;
    else if (Pos[toVar(data[i])] >= solver.qhead) ++nUndef;
  }
  if (nUndef + nTrue == 0) {
    std::cout << "Clause iID " << iID << " is conflicting." << std::endl;
    abort();
  }
  else if (nTrue == 0 and nUndef == 1) {
    std::cout << "Clause iID " << iID << " is not completely propagated" << std::endl;
    abort();
  }
}

// Debug method.
template <typename CF, typename DG>
void Counting<CF, DG>::allLitsPropagated(const Solver& solver, const int iID)  {
  auto& Pos = solver.Pos;
  const SlackMC& smc = solver.slackMCoefV[iID];
  assert(smc.isVal);
  long long saved = smc.slackMC;

  DG slkMC = -degr - data[0].c;
  for (int i = 0; i < (int)size(); ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slkMC += data[i].c;
    }
  }
  if (saved != slkMC) {
    std::cout << "Counting SLACK ERROR: iID " << iID << ", saved " << saved << ", real is " << slkMC << ", nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
    abort();
  }
  DG slack = slkMC + data[0].c;
  assert(slack >= 0);
  for (unsigned int i = 0; i < size() and data[i].c > slack; ++i) {
    Lit l = data[i].l;
    CF  c = data[i].c;
    if (isUnknown(Pos, l)) {
      std::cout << "Counting PROP ERROR: ctr iID " << iID << " has lit " << l << " not propagated. idx " << i << ", coef " << c << ", slack " << slack << ", slkMC " << slkMC << std::endl;
      std::cout << "nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
      abort();
    }
  }
}

// Debug method.
template <typename CF, typename DG>
void Watched<CF, DG>::allLitsPropagated(const Solver& solver, const int iID)  {
  auto& Pos = solver.Pos;
  const SlackMC& smc = solver.slackMCoefV[iID];
  assert(smc.isVal);
  long long saved = smc.slackMC;

  DG slkMC = -degr - aux::abs(data[0].c);
  for (int i = 0; i < (int)size(); ++i) {
    if (data[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i)))) {
      slkMC += aux::abs(data[i].c);
    }
  }
  if (saved != slkMC) {
    std::cout << "Watched SLACK ERROR: iID " << iID << ", saved " << saved << ", real is " << slkMC << ", nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
    abort();
  }
  DG slack = slkMC + aux::abs(data[0].c);
  assert(slack >= 0);
  for (unsigned int i = 0; i < size() and aux::abs(data[i].c) > slack; ++i) {
    Lit l = data[i].l;
    CF  c = data[i].c;
    if (isUnknown(Pos, l)) {
      std::cout << "Watched PROP ERROR: ctr iID " << iID << " has lit " << l << " not propagated. idx " << i << ", coef " << c << ", slack " << slack << ", slkMC " << slkMC << std::endl;
      std::cout << "nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
      abort();
    }
  }
}

// Debug method.
template <typename CF, typename DG>
void CountingSafe<CF, DG>::allLitsPropagated(const Solver& solver, const int iID) {
  auto& Pos = solver.Pos;
  CF maxCoef = aux::abs(terms[0].c);
  DG slkMC = -*degr - maxCoef;
  for (int i = 0; i < (int)size(); ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slkMC += terms[i].c;
    }
  }
  const SlackMC & smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = *((DG*)(aux::abs(smc.slackMC)));
  if (v != slkMC) {
    std::cout << "CountingSafe SLACK ERROR: iID " << iID << " has saved slackMC " << v << ", but real is " << slkMC << ", maxCoef " << maxCoef << ", nDecs " << stats.NDECIDE << ", nConfs " << stats.NCONFL << std::endl;
    abort();
  }
  DG slack = slkMC + maxCoef;
  assert(slack >= 0);
  for (int i = 0; i < (int)size() and terms[i].c > slack; ++i) {
    Lit l = terms[i].l;
    CF  c = terms[i].c;
    if (isUnknown(Pos, l)) {
      std::cout << "CountingSafe PROP ERROR: ctr iID " << iID << " has lit " << l << " not propagated. idx " << i << ", coef " << c << ", slack " << slack << ", slackMC " << slkMC  << ", maxCoef " << maxCoef << std::endl;
      std::cout << "nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << std::endl;
      abort();
    }
  }
}

// Debug method.
template <typename CF, typename DG>
void WatchedSafe<CF, DG>::allLitsPropagated(const Solver& solver, const int iID)  {
  auto& Pos = solver.Pos;
  CF maxCoef = aux::abs(terms[0].c);

  DG slkMC = -*degr - maxCoef;
  for (int i = 0; i < (int)size(); ++i) {
    if (terms[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i)))) {
      slkMC += aux::abs(terms[i].c);
    }
  }
  const SlackMC& smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = *((DG*)(aux::abs(smc.slackMC)));
  if (v != slkMC) {
    std::cout << "WatchedSafe SLACK ERROR: iID " << iID << " has saved slackMC " << v << ", but real is " << slkMC << ", nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
    abort();
  }
  DG slack = slkMC + maxCoef;
  assert(slack >= 0);
  for (unsigned int i = 0; i < size() and aux::abs(terms[i].c) > slack; ++i) {
    Lit l = terms[i].l;
    CF  c = terms[i].c;
    if (isUnknown(Pos, l)) {
      std::cout << "WatchedSafe PROP ERROR: ctr iID " << iID << " has lit " << l << " not propagated. idx " << i << ", coef " << c << ", slack " << slack << ", slkMC " << slkMC << std::endl;
      std::cout << "nDecs " << stats.NDECIDE << " nConfs " << stats.NCONFL << ", dl " << solver.decisionLevel() << std::endl;
      abort();
    }
  }
}


// Debug method.
template <typename CF, typename DG>
bool Counting<CF, DG>::hasCorrectSlack(const Solver& solver, const int iID) {
  return true;
  DG slk = -degr - data[0].c;
  for (int i = 0; i < (int)size(); ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slk += data[i].c;
    }
  }
  return (slk == static_cast<DG>(solver.slackMCoefV[iID].slackMC));
}

// Debug method.
template <typename CF, typename DG>
bool Watched<CF, DG>::hasCorrectSlack(const Solver& solver, const int iID) {
  return true;
  DG slk = -degr - aux::abs(data[0].c);
  for (int i = 0; i < (int)size(); ++i) {
    if (data[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))))
      slk += aux::abs(data[i].c);
  }
  return (slk == static_cast<DG>(solver.slackMCoefV[iID].slackMC));
}

// Debug method.
template <typename CF, typename DG>
bool CountingSafe<CF, DG>::hasCorrectSlack(const Solver& solver, const int iID) {
  return true;
  DG slkMC = -*degr - terms[0].c;
  for (int i = 0; i < (int)size(); ++i) {
    if (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))) {
      slkMC += terms[i].c;
    }
  }
  const SlackMC & smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = *((DG*)(aux::abs(smc.slackMC)));

  return (v == slkMC);
}

// Debug method.
template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::hasCorrectSlack(const Solver& solver, const int iID) {
  return true;
  DG slkMC = -*degr - aux::abs(terms[0].c);
  for (int i = 0; i < (int)size(); ++i) {
    if (terms[i].c < 0 && (solver.getPos()[toVar(lit(i))] >= solver.qhead || !isFalse(solver.getLevel(), lit(i))))
      slkMC += aux::abs(terms[i].c);
  }
  const SlackMC & smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = *((DG*)(aux::abs(smc.slackMC)));

  return (v == slkMC);
}

// Debug method.
template <typename CF, typename DG>
bool Watched<CF, DG>::hasCorrectWatches(const Solver& solver, const int iID) {
  return true;
  const SlackMC & smc = solver.slackMCoefV[iID];
  assert(smc.isVal);
  if (smc.slackMC >= 0) return true;
  for (int i = 0; i < (int)nextWatchIdx; ++i) assert(!isUnknown(solver.getPos(), lit(i)));
  for (int i = 0; i < (int)size(); ++i) {
    if (!(data[i].c < 0 || isFalse(solver.getLevel(), data[i].l))) {
      std::cout << i << " " << data[i].c << " " << isFalse(solver.getLevel(), data[i].l) << std::endl;
      print(solver);
    }
    assert(data[i].c < 0 || isFalse(solver.getLevel(), data[i].l));
  }
  return true;
}

// Debug method.
template <typename CF, typename DG>
bool WatchedSafe<CF, DG>::hasCorrectWatches(const Solver& solver, const int iID) {
  return true;
  const SlackMC & smc = solver.slackMCoefV[iID];
  assert(!smc.isVal);
  DG& v = *((DG*)(aux::abs(smc.slackMC)));
  if (v >= 0) return true;
  for (int i = 0; i < (int)nextWatchIdx; ++i) assert(!isUnknown(solver.getPos(), lit(i)));
  for (int i = 0; i < (int)size(); ++i) {
    if (!(terms[i].c < 0 || isFalse(solver.getLevel(), terms[i].l))) {
      std::cout << i << " " << terms[i].c << " " << isFalse(solver.getLevel(), terms[i].l) << std::endl;
      print(solver);
    }
    assert(terms[i].c < 0 || isFalse(solver.getLevel(), terms[i].l));
  }
  return true;
}

template <typename CF, typename DG>
void Watched<CF, DG>::resetWatches() {
  for (int i = 0; i < (int)size(); ++i) {
    data[i].c = aux::abs(data[i].c);
  }
  return;
}

template <typename CF, typename DG>
void WatchedSafe<CF, DG>::resetWatches() {
  for (int i = 0; i < (int)size(); ++i) {
    terms[i].c = aux::abs(terms[i].c);
  }
  return;
}

template struct Counting<int, long long>;

template struct Watched<int, long long>;

template struct CountingSafe<long long, int128>;
template struct CountingSafe<int128, int128>;
template struct CountingSafe<bigint, bigint>;

template struct WatchedSafe<long long, int128>;
template struct WatchedSafe<int128, int128>;
template struct WatchedSafe<bigint, bigint>;

}  // namespace rs

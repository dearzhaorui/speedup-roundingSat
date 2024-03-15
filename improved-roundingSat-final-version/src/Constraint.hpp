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

#include <algorithm>
#include <memory>
#include <sstream>
#include "IntSet.hpp"
#include "Logger.hpp"
#include "SimpleCons.hpp"
#include "Stats.hpp"
#include "aux.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

enum AssertionStatus { NONASSERTING, ASSERTING, FALSIFIED };

template <typename T>
inline T mir_coeff(const T& ai, const T& b, const T& d) {
  assert(d > 0);
  T bmodd = aux::mod_safe(b, d);
  return bmodd * aux::floordiv_safe(ai, d) + std::min(aux::mod_safe(ai, d), bmodd);
}

template <typename SMALL, typename LARGE>  // LARGE should be able to fit sums of SMALL
struct Constraint {
  LARGE degree = 0;
  LARGE rhs = 0;
  ID id = ID_Trivial;
  std::vector<Var> vars;
  std::vector<SMALL> coefs;
  std::stringstream proofBuffer;
  std::shared_ptr<Logger> plogger;
  static constexpr SMALL _unused_() { return std::numeric_limits<SMALL>::max(); }
  static constexpr LARGE _invalid_() { return std::numeric_limits<LARGE>::min(); }

  Constraint() {
    assert(std::numeric_limits<SMALL>::is_specialized);
    assert(std::numeric_limits<LARGE>::is_specialized);
    reset();
  }

  inline void resize(size_t s) {
    if (s > coefs.size()) coefs.resize(s, _unused_());
  }

  void resetBuffer(ID proofID = ID_Trivial) {
    assert(plogger);
    assert(proofID != ID_Undef);
    assert(proofID != ID_Unsat);
    proofBuffer.clear();
    proofBuffer.str(std::string());
    proofBuffer << proofID << " ";
  }
  void initializeLogging(std::shared_ptr<Logger>& l) {
    assert(isReset());
    plogger = l;
    if (plogger) resetBuffer();
  }
  template <typename T>
  inline static std::string proofMult(T mult) {
    std::stringstream ss;
    if (mult != 1) ss << mult << " * ";
    return ss.str();
  }

  bool isReset() const { return vars.size() == 0 && rhs == 0; }
  void reset() {
    for (Var v : vars) coefs[v] = _unused_();
    vars.clear();
    rhs = 0;
    degree = 0;
    id = ID_Trivial;
    if (plogger) resetBuffer();
  }

  inline void addRhs(LARGE r) {
    rhs += r;
    if (degree != _invalid_()) degree += r;
  }
  inline LARGE getRhs() const { return rhs; }
  inline LARGE getDegree() {
    if (degree != _invalid_()) return degree;
    degree = rhs;
    for (Var v : vars) degree -= std::min<SMALL>(0, coefs[v]);  // considering negative coefficients
    return degree;
  }
  inline SMALL getCoef(Lit l) const {
    assert((unsigned int)std::abs(l) < coefs.size());
    return coefs[std::abs(l)] == _unused_() ? 0 : (l < 0 ? -coefs[-l] : coefs[l]);
  }
  inline Lit getLit(Lit l) const {  // NOTE: answer of 0 means coef 0 or not in vars
    Var v = std::abs(l);
    if (v >= (Var)coefs.size()) return 0;
    SMALL c = coefs[v];
    if (c == 0 || c == _unused_())
      return 0;
    else if (c < 0)
      return -v;
    else
      return v;
  }
  inline bool falsified(const IntVecIt& level, Var v) const {
    assert(v > 0);
    assert((getLit(v) != 0 && !isFalse(level, getLit(v))) == (coefs[v] > 0 && !isFalse(level, v)) ||
           (coefs[v] < 0 && !isTrue(level, v)));
    return (coefs[v] > 0 && isFalse(level, v)) || (coefs[v] < 0 && isTrue(level, v));
  }
  inline bool increasesSlack(const IntVecIt& level, Var v) const {
    return isTrue(level, v) || (!isFalse(level, v) && coefs[v] > 0);
  }
  LARGE getSlack(const IntVecIt& level) const {
    LARGE slack = -rhs;
    for (Var v : vars)
      if (increasesSlack(level, v)) slack += coefs[v];
    return slack;
  }
  LARGE getSlack(const IntSet& assumptions) const {
    LARGE slack = -rhs;
    for (Var v : vars)
      if (assumptions.has(v) || (!assumptions.has(-v) && coefs[v] > 0)) slack += coefs[v];
    return slack;
  }

  // NOTE: erasing variables with coef 0 in addLhs would lead to invalidated iteration (e.g., for loops that weaken)
  void addLhs(SMALL c, Lit l) {  // treats negative literals as 1-v
    assert(l != 0);
    degree = _invalid_();
    Var v = l;
    if (l < 0) {
      rhs -= c;
      c = -c;
      v = -l;
    }
    assert(v < (Var)coefs.size());
    if (coefs[v] == _unused_()) vars.push_back(v), coefs[v] = 0;
    coefs[v] += c;
  }
  inline void weaken(SMALL m, Lit l) {  // add m*(l>=0) if m>0 and -m*(-l>=-1) if m<0
    if (m == 0) return;
    if (plogger) {
      if (m > 0)
        proofBuffer << (l < 0 ? "~x" : "x") << std::abs(l) << " " << proofMult(m) << "+ ";
      else
        proofBuffer << (l < 0 ? "x" : "~x") << std::abs(l) << " " << proofMult(-m) << "+ ";
    }
    addLhs(m, l);  // resets degree // TODO: optimize this method by not calling addLhs and not resetting degree
    if (m < 0) addRhs(m);
  }

  // @post: preserves order of vars
  void removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos, bool doSaturation = true) {
    if (plogger) {
      for (Var v : vars) {
        Lit l = getLit(v);
        SMALL c = getCoef(l);
        if (l == 0) continue;
        if (isUnit(level, l))
          proofBuffer << (l < 0 ? "x" : "~x") << v << " " << proofMult(c) << "+ ";
        else if (isUnit(level, -l))
          proofBuffer << plogger->unitIDs[pos[v]] << " " << proofMult(c) << "+ ";
      }
    }
    int j = 0;
    for (int i = 0; i < (int)vars.size(); ++i) {
      Var v = vars[i];
      SMALL c = coefs[v];
      if (c == 0)
        coefs[v] = _unused_();
      else if (isUnit(level, v)) {
        rhs -= c;
        if (degree != _invalid_() && c > 0) degree -= c;
        coefs[v] = _unused_();
      } else if (isUnit(level, -v)) {
        if (degree != _invalid_() && c < 0) degree += c;
        coefs[v] = _unused_();
      } else
        vars[j++] = v;
    }
    vars.resize(j);
    if (doSaturation) saturate();
  }
  bool hasNoUnits(const IntVecIt& level) const {
    for (Var v : vars)
      if (isUnit(level, v) || isUnit(level, -v)) return false;
    return true;
  }

  // @post: mutates order of vars
  void removeZeroes() {
    for (int i = 0; i < (int)vars.size(); ++i) {
      Var v = vars[i];
      if (coefs[v] == 0) {
        coefs[v] = _unused_();
        aux::swapErase(vars, i--);
      }
    }
  }
  bool hasNoZeroes() const {
    for (Var v : vars)
      if (coefs[v] == 0) return false;
    return true;
  }

  // @post: preserves order of vars
  void saturate(const std::vector<Var>& vs) {
    if (plogger && !isSaturated()) proofBuffer << "s ";  // log saturation only if it modifies the constraint
    LARGE w = getDegree();
    if (w <= 0) {  // NOTE: does not call reset(0), as we do not want to reset the buffer
      for (Var v : vars) coefs[v] = _unused_();
      vars.clear();
      rhs = 0;
      degree = 0;
      return;
    }
    for (Var v : vs) {
      if (coefs[v] < -w)
        rhs -= coefs[v] + w, coefs[v] = -w;
      else
        coefs[v] = std::min<LARGE>(coefs[v], w);
    }
    assert(isSaturated());
  }
  void saturate() { saturate(vars); }
  bool isSaturated() {
    LARGE w = getDegree();
    for (Var v : vars)
      if (std::abs(coefs[v]) > w) return false;
    return true;
  }

  template <typename S, typename L>
  void copyTo(Constraint<S, L>& out) const {
    assert(out.isReset());
    out.rhs = rhs;
    out.id = id;
    out.vars = vars;
    out.resize(coefs.size());
    for (Var v : vars) out.coefs[v] = coefs[v];
    if (degree == _invalid_())
      out.degree = out._invalid_();
    else
      out.degree = degree;
    if (plogger) {
      out.proofBuffer.str(std::string());
      out.proofBuffer << proofBuffer.str();
    }
  }

  template <typename CF, typename DG>
  void construct(const SimpleCons<CF, DG>& sc) {
    assert(isReset());
    assert(std::abs(sc.rhs) < std::numeric_limits<LARGE>::max());
    addRhs(sc.rhs);
    for (auto& t : sc.terms) {
      assert(std::abs(t.c) < std::numeric_limits<SMALL>::max());
      addLhs(t.c, t.l);
    }
    degree = _invalid_();
    id = sc.id;
    if (plogger) resetBuffer(id);
  }

  void invert() {
    rhs = -rhs;
    for (Var v : vars) coefs[v] = -coefs[v];
    degree = _invalid_();
  }

  template <typename S, typename L>
  void addUp(Constraint<S, L>& c, SMALL cmult = 1, SMALL thismult = 1) {
    assert(cmult >= 0);
    assert(thismult >= 0);
    if (plogger) proofBuffer << proofMult(thismult) << c.proofBuffer.str() << proofMult(cmult) << "+ ";
    if (thismult != 1) {
      rhs *= thismult;
      for (Var v : vars) coefs[v] *= thismult;
    }
    assert(std::abs(c.getRhs()) < std::numeric_limits<LARGE>::max());
    rhs += (LARGE)cmult * (LARGE)c.getRhs();
    for (Var v : c.vars) {
      assert(v < (Var)coefs.size());
      assert(v > 0);
      assert(std::abs(c.coefs[v]) < std::numeric_limits<SMALL>::max());
      SMALL val = cmult * c.coefs[v];
      if (coefs[v] == _unused_()) {
        vars.push_back(v);
        coefs[v] = val;
      } else {
        SMALL cf = coefs[v];
        if ((cf < 0) != (val < 0)) degree -= std::min(std::abs(cf), std::abs(val));
        coefs[v] = cf + val;
      }
    }
    degree = _invalid_();
  }

  void saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening) {
    removeZeroes();
    saturate();
    if (getDegree() >= (LARGE)INF) {
      LARGE div = aux::ceildiv<LARGE>(getDegree(), INF - 1);
      weakenNonDivisibleNonFalsifieds(level, div, fullWeakening);
      divideRoundUp(div);
      saturate();
    }
    assert(getDegree() < (LARGE)INF);
  }

  void multiply(const SMALL m) {
    assert(m > 0);
    if (m == 1) return;
    if (plogger) proofBuffer << proofMult(m);
    for (Var v : vars) coefs[v] *= m;
    rhs *= m;
    if (degree != _invalid_()) degree *= m;
  }

  void divide(const LARGE d) {
    if (plogger) proofBuffer << d << " d ";
    for (Var v : vars) {
      assert(coefs[v] % d == 0);
      coefs[v] /= d;
    }
    // NOTE: as all coefficients are divisible by d, we can aux::ceildiv the rhs instead of the degree
    rhs = aux::ceildiv_safe(rhs, d);
    if (degree != _invalid_()) degree = aux::ceildiv_safe(degree, d);
  }

  void divideRoundUp(const LARGE d) {
    assert(d > 0);
    if (d == 1) return;
    for (Var v : vars) {
      if (coefs[v] % d == 0) continue;
      weaken((coefs[v] < 0 ? 0 : d) - aux::mod_safe<LARGE>(coefs[v], d), v);
    }
    divide(d);
  }

  void weakenDivideRound(const IntVecIt& level, Lit l, bool maxdiv, bool fullWeakening) {
    assert(getCoef(l) > 0);
    LARGE div = maxdiv ? getCoef(l) : std::max<LARGE>(1, getSlack(level) + 1);
    weakenNonDivisibleNonFalsifieds(level, div, fullWeakening);
    divideRoundUp(div);
    saturate();
  }

  void applyMIR(LARGE d) {
    for (Var v : vars) coefs[v] = mir_coeff(coefs[v], rhs, d);
    rhs = aux::mod_safe(rhs, d) * aux::ceildiv_safe(rhs, d);
    degree = _invalid_();
    // TODO: fix logging
  }

  bool divideByGCD() {
    assert(isSaturated());
    assert(isSortedInDecreasingCoefOrder());
    assert(hasNoZeroes());
    if (vars.size() == 0) return false;
    if (std::abs(coefs[vars[0]]) >= INF) return false;  // TODO: large coefs currently unsupported
    unsigned int _gcd = std::abs(coefs[vars.back()]);
    for (Var v : vars) {
      _gcd = aux::gcd(_gcd, (unsigned int)std::abs(coefs[v]));
      if (_gcd == 1) return false;
    }
    assert(_gcd > 1);
    assert(_gcd < (unsigned int)INF);
    divide(_gcd);
    return true;
  }

  // NOTE: only equivalence preserving operations!
  void postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst, Stats& sts) {
    removeUnitsAndZeroes(level, pos);  // NOTE: also saturates
    if (sortFirst) sortInDecreasingCoefOrder();
    if (divideByGCD()) ++sts.NGCD;
    if (simplifyToCardinality(true)) ++sts.NCARDDETECT;
  }

  // NOTE: also removes encountered zeroes and changes variable order
  AssertionStatus isAssertingBefore(const IntVecIt& level, int lvl) {
    assert(lvl >= 0);
    assert(isSaturated());
    LARGE slack = -getDegree();
    SMALL largestCoef = std::numeric_limits<SMALL>::min();
    for (int i = vars.size() - 1; i >= 0; --i) {
      Var v = vars[i];
      SMALL cf = coefs[v];
      if (cf == 0) {
        coefs[v] = _unused_();
        aux::swapErase(vars, i);
        continue;
      }
      Lit l = cf < 0 ? -v : v;
      if (level[-l] < lvl) continue;  // falsified lit
      SMALL c = std::abs(cf);
      if (level[l] >= lvl) largestCoef = std::max(largestCoef, c);  // unknown lit
      slack += c;
      int mid = (vars.size() + i) / 2;  // move non-falsifieds to the back for efficiency in next call
      vars[i] = vars[mid];
      vars[mid] = v;
      if (slack >= getDegree()) return AssertionStatus::NONASSERTING;
    }
    if (slack >= largestCoef)
      return AssertionStatus::NONASSERTING;
    else if (slack >= 0)
      return AssertionStatus::ASSERTING;
    else
      return AssertionStatus::FALSIFIED;
  }

  // @return: earliest decision level that propagates a variable
  int getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const {
    assert(hasNoZeroes());
    assert(isSortedInDecreasingCoefOrder());
    assert(hasNoUnits(level));
    // calculate slack at level 0
    LARGE slack = -rhs;
    for (Var v : vars) slack += std::max(0, coefs[v]);
    if (slack < 0) return -1;

    // create useful datastructures
    std::vector<Lit> litsByPos;
    litsByPos.reserve(vars.size());
    for (Var v : vars) {
      Lit l = getLit(v);
      assert(l != 0);
      if (isFalse(level, l)) litsByPos.push_back(-l);
    }
    std::sort(litsByPos.begin(), litsByPos.end(),
              [&](Lit l1, Lit l2) { return pos[std::abs(l1)] < pos[std::abs(l2)]; });

    // calculate earliest propagating decision level by decreasing slack one decision level at a time
    auto posIt = litsByPos.cbegin();
    auto coefIt = vars.cbegin();
    int assertionLevel = 0;
    while (true) {
      while (posIt != litsByPos.cend() && level[*posIt] <= assertionLevel) {
        slack -= std::abs(coefs[std::abs(*posIt)]);
        ++posIt;
      }
      if (slack < 0) return assertionLevel - 1;
      while (coefIt != vars.cend() && assertionLevel >= level[getLit(*coefIt)]) ++coefIt;
      if (coefIt == vars.cend()) return INF;  // no assertion level
      if (slack < std::abs(coefs[*coefIt])) return assertionLevel;
      if (posIt == litsByPos.cend()) return INF;  // slack will no longer decrease
      assertionLevel = level[*posIt];
    }
  }

  // @post: preserves order after removeZeroes()
  void weakenNonImplied(const IntVecIt& level, LARGE slack, Stats& sts) {
    for (Var v : vars)
      if (coefs[v] != 0 && std::abs(coefs[v]) <= slack && !falsified(level, v)) {
        weaken(-coefs[v], v);
        ++sts.NWEAKENEDNONIMPLIED;
      }
    // TODO: always saturate?
  }
  // @post: preserves order after removeZeroes()
  bool weakenNonImplying(const IntVecIt& level, SMALL propCoef, LARGE slack, Stats& sts) {
    assert(hasNoZeroes());
    assert(isSortedInDecreasingCoefOrder());
    long long oldCount = sts.NWEAKENEDNONIMPLYING;
    for (int i = vars.size() - 1; i >= 0 && slack + std::abs(coefs[vars[i]]) < propCoef; --i) {
      Var v = vars[i];
      if (falsified(level, v)) {
        SMALL c = coefs[v];
        slack += std::abs(c);
        weaken(-c, v);
        ++sts.NWEAKENEDNONIMPLYING;
      }
    }
    bool changed = oldCount != sts.NWEAKENEDNONIMPLYING;
    if (changed) saturate();  // TODO: always saturate?
    return changed;
  }
  // @post: preserves order after removeZeroes()
  void heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, LARGE slk, Stats& sts) {
    assert(slk == getSlack(level));
    if (slk < 0) return;  // no propagation, no idea what to weaken
    assert(isSortedInDecreasingCoefOrder());
    Var v_prop = -1;
    for (int i = vars.size() - 1; i >= 0; --i) {
      Var v = vars[i];
      if (std::abs(coefs[v]) > slk && isUnknown(pos, v)) {
        v_prop = v;
        break;
      }
    }
    if (v_prop == -1) return;  // no propagation, no idea what to weaken
    if (weakenNonImplying(level, std::abs(coefs[v_prop]), slk, sts)) slk = getSlack(level);  // slack changed
    assert(getSlack(level) < std::abs(coefs[v_prop]));
    weakenNonImplied(level, slk, sts);
  }

  // @post: preserves order
  template <typename T>
  void weakenSmalls(T limit) {
    for (Var v : vars)
      if (std::abs(coefs[v]) < limit) weaken(-coefs[v], v);
    saturate();
  }

  void weakenNonDivisibleNonFalsifieds(const IntVecIt& level, LARGE div, bool fullWeakening) {
    assert(div > 0);
    if (div == 1) return;
    if (fullWeakening) {
      for (Var v : vars)
        if (coefs[v] % div != 0 && !falsified(level, v)) weaken(-coefs[v], v);
    } else {
      for (Var v : vars)
        if (coefs[v] % div != 0 && !falsified(level, v)) weaken(-(std::abs(coefs[v]) % div), (coefs[v] < 0 ? -v : v));
    }
  }

  LARGE absCoeffSum() const {
    LARGE result = 0;
    for (Var v : vars) result += std::abs(coefs[v]);
    return result;
  }

  // @post: preserves order of vars
  bool simplifyToCardinality(bool equivalencePreserving) {
    assert(isSaturated());
    assert(isSortedInDecreasingCoefOrder());
    assert(hasNoZeroes());
    if (vars.size() == 0 || std::abs(coefs[vars[0]]) == 1) return false;  // already cardinality
    const LARGE w = getDegree();
    if (w <= 0) return false;

    int largeCoefsNeeded = 0;
    LARGE largeCoefSum = 0;
    while (largeCoefsNeeded < (int)vars.size() && largeCoefSum < w) {
      largeCoefSum += std::abs(coefs[vars[largeCoefsNeeded]]);
      ++largeCoefsNeeded;
    }
    assert(largeCoefsNeeded > 0);
    if (largeCoefSum < w) {
      for (Var v : vars) weaken(-coefs[v], v);
      return true;  // trivial inconsistency
    }

    int skippable = vars.size();  // counting backwards
    if (equivalencePreserving) {
      LARGE smallCoefSum = 0;
      for (int i = 1; i <= largeCoefsNeeded; ++i) smallCoefSum += std::abs(coefs[vars[vars.size() - i]]);
      if (smallCoefSum < w) return false;
      // else, we have an equivalent cardinality constraint
    } else {
      LARGE wiggleroom = w - largeCoefSum + std::abs(coefs[vars[largeCoefsNeeded - 1]]);
      assert(wiggleroom > 0);
      while (skippable > 0 && wiggleroom > std::abs(coefs[vars[skippable - 1]])) {
        --skippable;
        wiggleroom -= std::abs(coefs[vars[skippable]]);
      }
    }
    assert(skippable >= largeCoefsNeeded);

    if (plogger) {
      SMALL div_coef = std::abs(coefs[vars[largeCoefsNeeded - 1]]);
      for (int i = 0; i < largeCoefsNeeded; ++i) {  // partially weaken large vars
        Lit l = getLit(vars[i]);
        SMALL d = getCoef(l) - div_coef;
        proofBuffer << (l > 0 ? "~x" : "x") << std::abs(l) << " " << proofMult(d) << "+ ";
      }
      for (int i = skippable; i < (int)vars.size(); ++i) {  // weaken small vars
        Lit l = getLit(vars[i]);
        SMALL d = getCoef(l);
        proofBuffer << (l > 0 ? "~x" : "x") << std::abs(l) << " " << proofMult(d) << "+ ";
      }
      if (div_coef > 1) proofBuffer << div_coef << " d ";
    }
    rhs = largeCoefsNeeded;
    degree = largeCoefsNeeded;
    vars.resize(skippable);
    for (int i = 0; i < (int)vars.size(); ++i) {
      SMALL& c = coefs[vars[i]];
      if (c < 0) {
        c = -1;
        --rhs;
      } else
        c = 1;
    }
    return true;
  }
  bool isCardinality() const {
    for (Var v : vars)
      if (std::abs(coefs[v]) > 1) return false;
    return true;
  }

  void sortInDecreasingCoefOrder() {
    std::sort(vars.begin(), vars.end(), [&](Var v1, Var v2) { return std::abs(coefs[v1]) > std::abs(coefs[v2]); });
  }
  bool isSortedInDecreasingCoefOrder() const {
    for (int i = 1; i < (int)vars.size(); ++i)
      if (std::abs(coefs[vars[i - 1]]) < std::abs(coefs[vars[i]])) return false;
    return true;
  }

  void logAsInput() {
    assert(plogger);
    toStreamAsOPB(plogger->formula_out);
    plogger->proof_out << "l " << ++plogger->last_formID << "\n";
    id = ++plogger->last_proofID;
    resetBuffer(id);  // ensure consistent proofBuffer
  }

  void logProofLine() {  // TODO: avoid successive proof log lines without any operations inbetween
    assert(plogger);
    plogger->proof_out << "p " << proofBuffer.str() << "0\n";
    id = ++plogger->last_proofID;
    resetBuffer(id);  // ensure consistent proofBuffer
#if !NDEBUG
    plogger->proof_out << "e " << id << " ";
    toStreamAsOPB(plogger->proof_out);
#endif
  }

  void logProofLineWithInfo(std::string&& info, const Stats& sts) {
    assert(plogger);
    _unused(info);
    _unused(sts);
#if !NDEBUG
    plogger->logComment(info, sts);
#endif
    logProofLine();
  }

  // @pre: reducible to unit over v
  void logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit, const Stats& sts) {
    assert(plogger);
    // reduce to unit over v
    removeUnitsAndZeroes(level, pos);
    assert(getLit(v_unit) != 0);
    for (Var v : vars)
      if (v != v_unit) weaken(-coefs[v], v);
    assert(getDegree() > 0);
    LARGE d = std::max<LARGE>(std::abs(coefs[v_unit]), getDegree());
    if (d > 1) proofBuffer << d << " d ";
    if (coefs[v_unit] > 0) {
      coefs[v_unit] = 1;
      rhs = 1;
    } else {
      coefs[v_unit] = -1;
      rhs = 0;
    }
    degree = 1;
    logProofLineWithInfo("Unit", sts);
    plogger->unitIDs.push_back(id);
  }

  void logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts) {
    assert(plogger);
    removeUnitsAndZeroes(level, pos);
    logProofLineWithInfo("Inconsistency", sts);
    assert(getSlack(level) < 0);
    plogger->proof_out << "c " << id << " 0" << std::endl;
  }

  void toStreamAsOPB(std::ofstream& o) {
    std::vector<Var> vs = vars;
    std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
    for (Var v : vs) {
      Lit l = getLit(v);
      if (l == 0) continue;
      o << "+" << getCoef(l) << (l < 0 ? " ~x" : " x") << v << " ";
    }
    o << ">= " << getDegree() << " ;\n";
  }
  void toStreamWithAssignment(std::ostream& o, const IntVecIt& level, const std::vector<int>& pos) {
    std::vector<Var> vs = vars;
    std::sort(vs.begin(), vs.end(), [](Var v1, Var v2) { return v1 < v2; });
    for (Var v : vs) {
      Lit l = getLit(v);
      if (l == 0) continue;
      o << getCoef(l) << "x" << l
        << (isUnknown(pos, l) ? "u"
                              : (isFalse(level, l) ? "f" + std::to_string(level[-l]) : "t" + std::to_string(level[l])))
        << " ";
    }
    o << ">= " << getDegree() << "(" << getSlack(level) << ")";
  }

  template <typename CF, typename DG>
  SimpleCons<CF, DG> toSimpleCons() {
    SimpleCons<CF, DG> result;
    result.rhs = getRhs();
    result.terms.reserve(vars.size());
    for (Var v : vars)
      if (coefs[v] != 0) result.terms.emplace_back((Coef)coefs[v], v);
    if (plogger) logProofLine();
    result.id = id;
    return result;
  }
};

template <typename S, typename L>
std::ostream& operator<<(std::ostream& o, Constraint<S, L>& C) {
  std::vector<Var> vars = C.vars;
  std::sort(vars.begin(), vars.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vars) {
    Lit l = C.coefs[v] < 0 ? -v : v;
    o << C.getCoef(l) << "x" << l << " ";
  }
  o << ">= " << C.getDegree();
  return o;
}

using intConstr = Constraint<int, long long>;
using longConstr = Constraint<long long, __int128>;
using int128Constr = Constraint<__int128, __int128>;
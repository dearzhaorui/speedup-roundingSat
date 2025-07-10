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
#include <sstream>
#include "ConstrSimple.hpp"
#include "ProofBuffer.hpp"
#include "SolverStructs.hpp"
#include "auxmath.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

namespace rs {

struct IntSet;
class Logger;

enum class AssertionStatus { NONASSERTING, ASSERTING, FALSIFIED };

// shared_ptr-like wrapper around ConstrExp, ensuring it gets released back to the pool when no longer needed.
template <typename CE>
struct CePtr {
  CE* ce;

  // default constructor
  CePtr() : ce(nullptr) {}
  // regular constructor
  CePtr(CE* c) : ce(c) {
    if (ce) ce->increaseUsage();
  }
  // copy constructor
  CePtr(const CePtr<CE>& other) : ce{other.ce} {
    if (ce) ce->increaseUsage();
  }
  // copy constructor allowing for polymorphism
  template <typename T, typename = std::enable_if_t<std::is_convertible_v<T&, CE&>>>
  CePtr(const CePtr<T>& other) : ce{other.ce} {
    if (ce) ce->increaseUsage();
  }
  // move constructor
  CePtr(CePtr<CE>&& other) : ce{other.ce} { other.ce = nullptr; }
  // move constructor allowing for polymorphism
  template <typename T, typename = std::enable_if_t<std::is_convertible_v<T&, CE&>>>
  CePtr(CePtr<T>&& other) : ce{other.ce} {
    other.ce = nullptr;
  }
  // destructor
  ~CePtr() {
    if (ce) ce->decreaseUsage();
  }
  // assignment operator
  CePtr<CE>& operator=(const CePtr<CE>& other) {
    if (this == &other) return *this;
    if (ce) ce->decreaseUsage();
    ce = other.ce;
    if (ce) ce->increaseUsage();
    return *this;
  }
  // move assignment operator
  CePtr<CE>& operator=(CePtr<CE>&& other) {
    if (this == &other) return *this;
    if (ce) ce->decreaseUsage();
    ce = other.ce;
    other.ce = nullptr;
    return *this;
  }

  CE& operator*() const { return *ce; }
  CE* operator->() const { return ce; }
  explicit operator bool() const { return ce; }
};

class ConstrExpPools;

struct ConstrExpSuper {
  std::vector<Var> vars;
  Origin orig = Origin::UNKNOWN;

  virtual ~ConstrExpSuper() {}

  virtual void increaseUsage() = 0;
  virtual void decreaseUsage() = 0;

  virtual void copyTo(Ce32 ce) const = 0;
  virtual void copyTo(Ce64 ce) const = 0;
  virtual void copyTo(Ce96 ce) const = 0;
  virtual void copyTo(Ce128 ce) const = 0;
  virtual void copyTo(CeArb ce) const = 0;

  virtual CeSuper clone(ConstrExpPools& ce) const = 0;
  virtual CRef toConstr(ConstraintAllocator& ca, bool locked, ID id) const = 0;
  virtual std::unique_ptr<ConstrSimpleSuper> toSimple() const = 0;

  virtual void resize(size_t s) = 0;
  virtual void resetProof(ID proofID) = 0;
  virtual ProofBuffer& getProof() = 0;
  virtual void initializeLogging(Logger* l) = 0;
  virtual void stopLogging() = 0;
  virtual bool isReset() const = 0;
  virtual void reset() = 0;

  virtual Lit getLit(Lit l) const = 0;
  virtual bool hasLit(Lit l) const = 0;

  virtual void weaken(Var v) = 0;
  virtual void weakenLast() = 0;

  virtual bool hasNegativeSlack(const IntVecIt& level) const = 0;
  virtual bool hasNegativeSlack(const IntSet& assumptions) const = 0;
  virtual bool isTautology() const = 0;
  virtual bool isInconsistency() const = 0;
  virtual bool isSatisfied(const IntVecIt& level) const = 0;

  virtual void removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos, 
                                    bool doSaturation = true, bool logIfTautology = true) = 0;
  virtual bool hasNoUnits(const IntVecIt& level) const = 0;
  virtual void removeZeroes() = 0;
  virtual bool hasNoZeroes() const = 0;

  virtual void saturate(const std::vector<Var>& vs, bool check = true) = 0;
  virtual void saturate(bool check = true) = 0;
  virtual bool isSaturated() const = 0;
  virtual void saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening, int bitOverflow, int bitReduce,
                                      Lit asserting) = 0;
  virtual void saturateAndFixOverflowRational(const std::vector<double>& lpSolution) = 0;
  virtual bool fitsInDouble() const = 0;
  virtual bool largestCoefFitsIn(int bits) const = 0;

  virtual void weakenDivideRound(const IntVecIt& level, Lit l, bool slackdiv, bool fullWeakening) = 0;

  virtual bool divideByGCD() = 0;
  virtual void postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst, Stats& sts) = 0;
  virtual AssertionStatus isAssertingBefore(const IntVecIt& level, int lvl) const = 0;
  virtual int getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const = 0;
  virtual void heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, Stats& sts) = 0;

  virtual bool simplifyToCardinality(bool equivalencePreserving) = 0;
  virtual void simplifyToClause() = 0;
  virtual bool isCardinality() const = 0;
  virtual int getCardinalityDegree() const = 0;
  virtual int getCardinalityDegreeWithZeroes() = 0;
  virtual void simplifyToMinLengthCardinality() = 0;
  virtual bool isClause() const = 0;
  virtual void sortInDecreasingCoefOrder(const std::function<bool(Var, Var)>& tiebreaker = [](Var, Var) {
    return false;
  }) = 0;
  virtual bool isSortedInDecreasingCoefOrder() const = 0;
  virtual void sort(const std::function<bool(Var, Var)>& comp) = 0;

  virtual ID logAsAssumption() = 0;
  virtual ID logInput() = 0;
  virtual ID logCG() = 0;
  virtual ID logRup() = 0;
  virtual ID logImplied() = 0;
  virtual void logAssertEquals(ID id) = 0;
  virtual ID logProofLine() = 0;
  virtual ID logProofLineWithInfo([[maybe_unused]] std::string&& info, [[maybe_unused]] const Stats& sts) = 0;
  virtual void logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit, const Stats& sts) = 0;
  virtual ID logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts) = 0;

  virtual void toStreamAsOPB(std::ostream& o) const = 0;
  virtual void toStreamWithAssignment(std::ostream& o, const IntVecIt& level, const std::vector<int>& pos) const = 0;

  virtual void resolveWith(Ce32 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos) = 0;
  virtual void resolveWith(Ce64 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos) = 0;
  virtual void resolveWith(Ce96 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos) = 0;
  virtual void resolveWith(Ce128 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos) = 0;
  virtual void resolveWith(CeArb c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos) = 0;
  virtual void resolveWith(const Clause& c, Lit l, IntSet* actSet, const IntVecIt& Level,
                           const std::vector<int>& Pos) = 0;
  virtual void resolveWith(const Cardinality& c, Lit l, IntSet* actSet, const IntVecIt& Level,
                           const std::vector<int>& Pos) = 0;
};

template <typename CE>
class ConstrExpPool;

// Dense representation of a constraint
// Consists of a dense vector of coefficients
// Used variables are tracked so that operation time depends on the local number of variables
// Variable order is not guaranteed, check individual functions for pre- and postconditions
// Both literal normal form (degree) and variable normal form (rhs) are kept consistent
template <typename SMALL, typename LARGE>  // LARGE should be able to fit sums of SMALL
struct ConstrExp final : public ConstrExpSuper {
 private:
  ConstrExpPool<ConstrExp<SMALL, LARGE>>& pool;
  long long usageCount = 0;

 public:
  LARGE degree = 0;
  LARGE rhs = 0;
  std::vector<SMALL> coefs;
  std::vector<bool> used;
  ProofBuffer proof;
  Logger* plogger = nullptr;

 private:
  void remove(Var v);
  bool increasesSlack(const IntVecIt& level, Var v) const;
  LARGE calcDegree() const;
  LARGE calcRhs() const;
  bool testConstraint() const;
  bool falsified(const IntVecIt& level, Var v) const;

 public:
  ConstrExp(ConstrExpPool<ConstrExp<SMALL, LARGE>>& cep);
  void increaseUsage();
  void decreaseUsage();

  void copyTo(Ce32 ce) const { copyTo_(ce); }
  void copyTo(Ce64 ce) const { copyTo_(ce); }
  void copyTo(Ce96 ce) const { copyTo_(ce); }
  void copyTo(Ce128 ce) const { copyTo_(ce); }
  void copyTo(CeArb ce) const { copyTo_(ce); }

  CeSuper clone(ConstrExpPools& ce) const;
  CePtr<ConstrExp<SMALL, LARGE>> cloneSameType(ConstrExpPools& ce) const;
  CRef toConstr(ConstraintAllocator& ca, bool locked, ID id) const;
  std::unique_ptr<ConstrSimpleSuper> toSimple() const;
  std::unique_ptr<ConstrSimple<SMALL, LARGE>> toSimpleSameType() const;

  void resize(size_t s);
  void resetProof(ID proofID) { proof.reset(proofID); }
  ProofBuffer& getProof() { return proof; }
  void initializeLogging(Logger* l);
  void stopLogging();

  bool isReset() const;
  void reset();

  LARGE getRhs() const;
  LARGE getDegree() const;
  SMALL getCoef(Lit l) const;
  SMALL getLargestCoef() const;
  SMALL getSmallestCoef() const;
  LARGE getCutoffVal() const;
  Lit getLit(Lit l) const;
  bool hasLit(Lit l) const;

  void addRhs(const LARGE& r);
  void addLhs(const SMALL& cf, Lit l);  // TODO: Term?
  void weaken(const SMALL& m, Var v);
  void weakenNoLog(const SMALL& m, Var v);
  void weaken(Var v);
  void weakenLast();

  LARGE getSlack(const IntVecIt& level) const;
  bool hasNegativeSlack(const IntVecIt& level) const;
  LARGE getSlack(const IntSet& assumptions) const;
  bool hasNegativeSlack(const IntSet& assumptions) const;
  bool isTautology() const;
  bool isInconsistency() const;
  bool isSatisfied(const IntVecIt& level) const;
  
  void logIfUnit(Lit l, const SMALL& c, const IntVecIt& level, const std::vector<int>& pos);
  void logIfUnitDelta(Lit l, const SMALL& c, const IntVecIt& level, const std::vector<int>& pos, 
                      std::vector<ID> &hints, int &nsimplified);
  void logUnits(const IntVecIt& level, const std::vector<int>& pos, bool logIfTautology);
  void logUnits(const Clause &c, const SMALL &cmult, const IntVecIt& level, const std::vector<int>& pos);
  void logUnits(const Cardinality &c, const SMALL &cmult, const IntVecIt& level, const std::vector<int>& pos);

  /**
   * @brief Remove literals in reason with coeff 0 and weaken away literals that are unit constraints in our database.
   *
   * @post: preserves order of vars
   */
  void removeUnitsAndZeroes(const IntVecIt& level, const std::vector<int>& pos, 
                            bool doSaturation = true, bool logIfTautology = true);
  bool hasNoUnits(const IntVecIt& level) const;
  // @post: mutates order of vars
  void removeZeroes();
  bool hasNoZeroes() const;

  /**
   * @brief Saturate the constraint.
   *
   * @tparam SMALL Coefficient type.
   * @tparam LARGE Degree type.
   * @param vs Vector of variable in the constraint.
   * @param check If true, check if constraint is already saturated and return directly if this is the case.
   *
   * @post preserves order of vars
   */
  void saturate(const std::vector<Var>& vs, bool check = true);
  /**
   * @brief Saturate the constraint.
   *
   * @tparam SMALL Coefficient type.
   * @tparam LARGE Degree type.
   * @param check If true, check if constraint is already saturated and return if this is the case.
   */
  void saturate(bool check = true);
  bool isSaturated() const;
  /**
   * @brief Saturate after resolution step and prevent overflow.
   *
   * @post saturated
   * @post nothing else if bitOverflow == 0
   * @post the largest coefficient is less than 2^bitOverflow
   * @post the degree and rhs are less than 2^bitOverflow * INF
   * @post if overflow happened, all division until 2^bitReduce happened
   * @post the constraint remains conflicting or propagating on asserting
   */
  void saturateAndFixOverflow(const IntVecIt& level, bool fullWeakening, int bitOverflow, int bitReduce, Lit asserting);
  /*
   * Fixes overflow for rationals
   * @post: saturated
   * @post: none of the coefficients, degree, or rhs exceed INFLPINT
   */
  void saturateAndFixOverflowRational(const std::vector<double>& lpSolution);
  bool fitsInDouble() const;
  bool largestCoefFitsIn(int bits) const;

  template <typename S, typename L>
  void addUp(CePtr<ConstrExp<S, L>> c, const SMALL& cmult = 1, const SMALL& thismult = 1) {
    assert(cmult >= 1);
    assert(thismult >= 1);
    if (plogger) proof.addConstraint(thismult, c->proof, cmult);
    if (thismult > 1) {
      degree *= thismult;
      rhs *= thismult;
      for (Var v : vars) coefs[v] *= thismult;
    }
    rhs += static_cast<LARGE>(cmult) * static_cast<LARGE>(c->rhs);
    degree += static_cast<LARGE>(cmult) * static_cast<LARGE>(c->degree);
    for (Var v : c->vars) {
      assert(v < (Var)coefs.size());
      assert(v > 0);
      SMALL val = cmult * static_cast<SMALL>(c->coefs[v]);
      if (!used[v]) {
        assert(coefs[v] == 0);
        vars.push_back(v);
        coefs[v] = val;
        used[v] = true;
      } else {
        if ((coefs[v] < 0) != (val < 0)) degree -= std::min(aux::abs(coefs[v]), aux::abs(val));
        coefs[v] += val;
      }
    }
  }

  template <typename S, typename L>
  void addUp(const ConstrSimple<S, L>& c, const SMALL& cmult = 1, const SMALL& thismult = 1) {
    assert(cmult >= 1);
    assert(thismult >= 1);
    if (plogger) {
      proof.addConstraint(thismult, c.proof, cmult);
    }
    if (thismult > 1) {
      degree *= thismult;
      rhs *= thismult;
      for (Var v : vars) coefs[v] *= thismult;
    }
    addRhs(static_cast<LARGE>(cmult) * static_cast<LARGE>(c.rhs));
    for (const auto& t : c.terms) addLhs(cmult * static_cast<SMALL>(t.c), t.l);
  }

  void invert();
  void multiply(const SMALL& m);
  void divide(const LARGE& d);
  /**
   * @brief Divides the current constraint by `d` and rounds up the coefficients and degree.
   *
   * @tparam SMALL Coefficient type.
   * @tparam LARGE Degree type.
   * @param d Divisor for the division.
   */
  void divideRoundUp(const LARGE& d);

  /**
   * @brief Initial RoundingSAT refinement function. Choose a divisor and make all coefficient of non-falsified literals
   * divisible by the divisor.
   *
   * @tparam SMALL Coefficient type.
   * @tparam LARGE Degree type.
   * @param level Data structure stating in which decision level and to which value variables are assigned.
   * @param l Literal to resolve over.
   * @param slackdiv If true, the divisor is reason constraint slack + 1. If false, divide by the literal coefficient in
   * the reason constraint.
   * @param fullWeakening If true, weaken literals completely. If false, weaken literals to biggest dividable
   * coefficient.
   */
  void weakenDivideRound(const IntVecIt& level, Lit l, bool slackdiv, bool fullWeakening);

  /**
   * @brief Weaken the constraint such that each coefficient of the non falsified literal in the constraint are
   * divisible by `div`.
   *
   * @param level Data structure stating in which decision level and to which value variables are assigned.
   * @param div Divisor to divide the constraint by in the resolution step.
   * @param fullWeakening If true, weaken literals completely. If false, weaken literals to biggest dividable
   * coefficient.
   * @param asserting The literal to resolve over in the resolution step.
   */
  void weakenNonDivisibleNonFalsifiedLog(const IntVecIt& level, const LARGE& div, bool fullWeakening, Lit asserting);
  void weakenNonDivisibleNonFalsified(const IntVecIt& level, const LARGE& div, bool fullWeakening, Lit asserting);
  void applyMIR(const LARGE& d, std::function<Lit(Var)> toLit);
  void applyDivCustomNormalization(const LARGE& d, std::function<Lit(Var)> toLit);

  bool divideByGCD();
  // NOTE: only equivalence preserving operations!
  void postProcess(const IntVecIt& level, const std::vector<int>& pos, bool sortFirst, Stats& sts);
  AssertionStatus isAssertingBefore(const IntVecIt& level, int lvl) const;
  // @return: earliest decision level that propagates a variable
  int getAssertionLevel(const IntVecIt& level, const std::vector<int>& pos) const;
  // @post: preserves order after removeZeroes()
  void weakenNonImplied(const IntVecIt& level, const LARGE& slack, Stats& sts);
  /**
   * @brief Weaken literals that are falsified and have a small enough coefficient at the current level.
   *
   * @post: preserves order after removeZeroes()
   *
   * @todo: return modified slack?
   */
  bool weakenNonImplying(const IntVecIt& level, const SMALL& propCoef, const LARGE& slack, Stats& sts);
  // @post: preserves order after removeZeroes()
  void heuristicWeakening(const IntVecIt& level, const std::vector<int>& pos, Stats& sts);

  // @post: preserves order
  template <typename T>
  void weakenSmalls(const T& limit) {
    for (Var v : vars)
      if (aux::abs(coefs[v]) < limit) weaken(v);
    saturate();
  }

  // zeroes out variables not in support
  void weakenOutsideSupport(const std::vector<Var>& support);

  LARGE absCoeffSum() const;

  // @post: preserves order of vars
  bool simplifyToCardinality(bool equivalencePreserving);
  bool isCardinality() const;
  int getCardinalityDegree() const;
  int getCardinalityDegreeWithZeroes();
  void simplifyToMinLengthCardinality();
  void simplifyToClause();
  bool isClause() const;

  void sortInDecreasingCoefOrder(const std::function<bool(Var, Var)>& tiebreaker = [](Var, Var) { return false; });
  bool isSortedInDecreasingCoefOrder() const;
  void sort(const std::function<bool(Var, Var)>& comp);

  ID logAsAssumption();
  ID logInput();
  ID logCG();
  ID logRup();
  ID logImplied();
  void logAssertEquals(ID id);
  ID logProofLine();
  ID logProofLineWithInfo([[maybe_unused]] std::string&& info, [[maybe_unused]] const Stats& sts);
  // @pre: reducible to unit over v
  void logUnit(const IntVecIt& level, const std::vector<int>& pos, Var v_unit, const Stats& sts);
  ID logInconsistency(const IntVecIt& level, const std::vector<int>& pos, const Stats& sts);

  void toStreamAsOPB(std::ostream& o) const;
  void toStreamWithAssignment(std::ostream& o, const IntVecIt& level, const std::vector<int>& pos) const;

  void resolveWith(Ce32 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(Ce64 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(Ce96 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(Ce128 c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(CeArb c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(const Clause& c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);
  void resolveWith(const Cardinality& c, Lit l, IntSet* actSet, const IntVecIt& Level, const std::vector<int>& Pos);

 private:
  void addUsedLitsToActiveSet(IntSet* actSet, Lit l, const IntVecIt& level);

  /**
   * @brief Refine the reason constraint such that the slack of the resolvent with the conflict constraint over `l` is
   * negative.
   *
   * @tparam CF Coefficient type.
   * @tparam DG Degree type.
   * @param reason Reason constraint.
   * @param l Literal to resolve over.
   * @param level Data structure stating in which decision level and to which value variables are assigned.
   * @param Pos Index vector over variables where the variable was assigned on the trail.
   */
  template <typename CF, typename DG>
  void refineConstrToNegativeSlackResolvent(CePtr<ConstrExp<CF, DG>> reason, Lit l, const IntVecIt& level,
                                            const std::vector<int>& Pos) {
    reason->removeUnitsAndZeroes(level, Pos);
    if (options.weakenNonImplying) reason->weakenNonImplying(level, reason->getCoef(l), reason->getSlack(level), stats);
    reason->saturateAndFixOverflow(level, (bool)options.weakenFull, options.bitsOverflow.get(),
                                   options.bitsReduced.get(), l);

    reason->weakenDivideRound(level, l, (bool)options.slackdiv, (bool)options.weakenFull);
  }

  template <typename CF, typename DG>
  void generalizedResolution(CePtr<ConstrExp<CF, DG>> reason, Lit l) {
    SMALL reason_coef_l = static_cast<SMALL>(reason->getCoef(l));  // NOTE: SMALL >= CF
    SMALL confl_coef_l = getCoef(-l);
    SMALL gcd_coef_l = aux::gcd(reason_coef_l, confl_coef_l);
    addUp(reason, confl_coef_l / gcd_coef_l, reason_coef_l / gcd_coef_l);
  }

  template <typename CF, typename DG>
  void genericResolve(CePtr<ConstrExp<CF, DG>> reason, Lit l, IntSet* actSet, const IntVecIt& level,
                      const std::vector<int>& Pos) {
    assert(getCoef(-l) > 0);
    stats.NADDEDLITERALS += reason->vars.size();

    refineConstrToNegativeSlackResolvent(reason, l, level, Pos);

    // Add used variables to active set.
    if (actSet != nullptr) {
      for (Var v : reason->vars) {
        Lit l = reason->getLit(v);
        addUsedLitsToActiveSet(actSet, l, level);
      }
    }

    generalizedResolution(reason, l);
    saturateAndFixOverflow(level, (bool)options.weakenFull, options.bitsOverflow.get(), options.bitsReduced.get(), 0);
    assert(getCoef(-l) == 0);
    assert(hasNegativeSlack(level));
  }

  template <typename S, typename L>
  void copyTo_(CePtr<ConstrExp<S, L>> out) const {
    // TODO: assert whether S/L can fit SMALL/LARGE? Not always possible.
    assert(out->isReset());
    out->degree = static_cast<L>(degree);
    out->rhs = static_cast<L>(rhs);
    out->orig = orig;
    out->vars = vars;
    assert(out->coefs.size() == coefs.size());
    for (Var v : vars) {
      out->coefs[v] = static_cast<S>(coefs[v]);
      assert(used[v] == true);
      assert(out->used[v] == false);
      out->used[v] = true;
    }
    if (plogger) {
      out->proof = proof;
    }
  }

  template <typename S, typename L>
  std::unique_ptr<ConstrSimple<S, L>> toSimple_() const {
    auto result = std::make_unique<ConstrSimple<S, L>>(std::vector<Term<S>>({}), static_cast<L>(rhs), orig);
    result->terms.reserve(vars.size());
    for (Var v : vars)
      if (coefs[v] != 0) result->terms.emplace_back(static_cast<S>(coefs[v]), v);
    if (plogger) result->proof = proof;
    return result;
  }
};

template <typename S, typename L>
std::ostream& operator<<(std::ostream& o, const ConstrExp<S, L>& C) {
  std::vector<Var> vars = C.vars;
  std::sort(vars.begin(), vars.end(), [](Var v1, Var v2) { return v1 < v2; });
  for (Var v : vars) {
    Lit l = C.coefs[v] < 0 ? -v : v;
    o << C.getCoef(l) << "x" << l << " ";
  }
  o << ">= " << C.degree;
  return o;
}

}  // namespace rs

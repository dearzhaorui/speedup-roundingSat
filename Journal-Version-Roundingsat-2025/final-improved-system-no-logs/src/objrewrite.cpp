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

#include "objrewrite.hpp"

#include "ConstrExp.hpp"
#include "ConstrExpPool.hpp"
#include "Logger.hpp"
#include "Solver.hpp"

namespace rs {

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::LazyVar(const ObjRewrite<SMALL, LARGE>& super, Var startVar) : 
    opt(super.opt),
    logger(super.logger), solver(super.solver), cePools(super.cePools),
    reformObj(super.reformObj), cost(super.cost),
    objLowerBound(super.objLowerBound), newLowerBound(opt.lower_bound), upperBound(super.upperBound), lastUpperBound(upperBound),
    coreID(logger), coreUBID(logger), refToOrigID(logger), objToCoreID(logger),
    atLeastUnprocessedID(logger),
    atLeastID(logger),
    atMostUnprocessedID(logger),
    atMostID(logger),
    sumReifiedID(logger) {
  // TODO: Check if we use stronger reification (knowing that the rhs of the reified constraint has a known minimum
  // size) and bidirectional reification.

  const Ce32& cardCore_ = super.cardCore;
  coveredVars = cardCore_->getDegree();
  reified = options.cgEncoding.is("reified");
  lastVar = 0;

  cardCore_->toSimple()->copyTo(atLeast);
  atLeast.toNormalFormLit();
  assert(atLeast.rhs == cardCore_->getDegree());

  atLeast.copyTo(atMost);
  atMost.rhs *= -1;
  for (Term<int>& t : atMost.terms) t.c *= -1;

  currentVar = startVar;
  atLeast.terms.emplace_back(-1, startVar);
  atMost.terms.emplace_back(remainingVars(), startVar);
  ++coveredVars;

  if (logger) {
    coreID = super.coreID;
    lastAtLeast = coreID;
    lastAtMost = ID_Undef;
    sumReified = ConstrSimple32({}, 0, Origin::COREGUIDED);
    if (options.cgCoreUpper) {
      cardCore_->toSimple()->copyTo(cardCore);
      refToOrigID = ID(opt.refToOrigID);
      if (upperBound < static_cast<int>(cardCore_->vars.size())) {
        objToCoreID = opt.getObjToCore(cardCore_, cost, refToOrigID, newLowerBound);
        refToOrigID = ID_Undef;
        coreUBID = opt.getCoreUB(cardCore_, cost, upperBound, objToCoreID);
      }
    }
  }
}

template <typename SMALL, typename LARGE>
LazyVar<SMALL, LARGE>::~LazyVar() {
  solver.dropExternal(atLeastID, false, false);
  solver.dropExternal(atMostID, false, false);
}

template <typename SMALL, typename LARGE>
int LazyVar<SMALL, LARGE>::remainingVars() const {
  return upperBound - coveredVars;
}

// WARNING: UNTESTED
// Note: the proof sometimes gives better bounds than what the solver estimates
// Maybe we should do a more exact calculation once the solver detects an improvement?
template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::setUpperBound(int cardUpperBound, ID UBID) {
  assert(cardUpperBound < upperBound);
  ++stats.COREUBIMPROVE;
  upperBound = cardUpperBound;
  assert(upperBound >= 0);
  if (logger) {
    logger->logComment("Improving Core UB");
    if (objToCoreID == ID_Undef) {
      objToCoreID = opt.getObjToCore(cardCore.toExpandedSameType(cePools), cost, refToOrigID, newLowerBound);
      refToOrigID = ID_Undef;
    }
    ProofBuffer proof;
    proof.reset(objToCoreID);
    proof.addClause(UBID, 1);
    proof << proofDiv(cost);
    coreUBID = proof.logPolish(*logger);
  }
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::addVar(Var v) {
  currentVar = v;
  if (reified) {
    Term<int>& last = atLeast.terms.back();
    last = {last.c - 1, v};
    --atMost.rhs;
    atMost.terms.back() = {remainingVars(), v};
  } else {
    atLeast.terms.emplace_back(-1, v);
    atMost.terms.back().c = 1;
    atMost.terms.emplace_back(remainingVars(), v);
  }
  ++coveredVars;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::logAtLeast() {
  if (not logger) return;
  logger->logComment("New reified variable =>");
  ProofBuffer& proof = atLeast.proof;
  proof.reset();
  proof.addWitness(currentVar, 0);
  ID contradictID = reified ? coreID : lastAtLeast;
  proof.addSubProof(contradictID);
  [[maybe_unused]] ID newID = proof.logRedundancy(*logger, &atLeast);
  //logger->protect.insert(newID);
}

template <typename SMALL, typename LARGE>
ID LazyVar<SMALL, LARGE>::addAtLeast() {
  assert(atLeast.terms.back().l == currentVar);
  solver.dropExternal(atLeastID, !reified, false);
  std::tie(atLeastUnprocessedID, atLeastID) = solver.addConstraint(atLeast, Origin::COREGUIDED);
  return atLeastID;
}

template <typename SMALL, typename LARGE>
void LazyVar<SMALL, LARGE>::logAtMost() {
  if (not logger) return;
  logger->logComment("New reified variable <=");
  ProofBuffer& proof = atMost.proof;
  proof.reset();
  if (reified or lastVar==0) {
    proof.addWitness(currentVar, 1);
    if (coreUBID != ID_Undef) {
      proof.addSubProof(coreUBID);
    }
  } else {
    std::pair<Var, Var> witness({currentVar, lastVar});
    proof.addWitness(std::span(&witness,1));
    // Witness maps new at most to last at most
    proof.addSubProof(atMostUnprocessedID);
  }
  [[maybe_unused]] ID newID = proof.logRedundancy(*logger, &atMost);
  //logger->protect.insert(newID);
}

template <typename SMALL, typename LARGE>
ID LazyVar<SMALL, LARGE>::addAtMost() {
  assert(atMost.terms.back().l == currentVar);
  solver.dropExternal(atMostID, !reified, false);
  std::tie(atMostUnprocessedID, atMostID) = solver.addConstraint(atMost, Origin::COREGUIDED);
  return atMostID;
}

template <typename SMALL, typename LARGE>
ID LazyVar<SMALL, LARGE>::addSymBreaking() const {
  assert(lastVar < currentVar);
  // y-- + ~y >= 1 (equivalent to y-- >= y)
  ConstrSimple32 c({{1, lastVar}, {1, -currentVar}}, 1);
  if (logger) {
    CeSuper ce = c.toExpanded(cePools);
    logger->logComment("New variable order");
    ce->resetProof(lastAtMost);
    ce->getProof().addClause(atLeastUnprocessedID, 1);
    ce->getProof() << proofDiv(std::numeric_limits<long long>::max());
    return solver.addTempConstraint(ce, Origin::COREGUIDED).second;
  } else {
    return solver.addConstraint(c, Origin::COREGUIDED).second;
  }
}

// WARNING: UNTESTED
template <typename SMALL, typename LARGE>
ID LazyVar<SMALL, LARGE>::improveAtMost(int newc, bool addToSolver) {
  assert(atMost.terms.back().l == currentVar);
  if (addToSolver) {
    solver.dropExternal(atMostID, !reified, false);
  }
  Term<int>& last = atMost.terms.back();
  int lastc = last.c;
  assert(lastc>newc);
  last = {newc, last.l};
  if (logger) {
    logger->logComment("Improved reified variable <=");
    ProofBuffer proof;
    if (reified) {
      proof.reset(atMostUnprocessedID);
      assert(coreUBID != ID_Undef);
      proof.addClause(coreUBID, lastc-1);
      proof << proofDiv(lastc);
    }
    else {
      proof.addWitness({});
      proof.beginSubProof();
      ProofBuffer add;
      add.resetRelative(-1);
      add.addConstraint(atMostUnprocessedID);
      add.saturate();
      proof.addSubProofStep(add);
      add.resetRelative(-2);
      add.addConstraint(coreUBID);
      proof.addSubProofStep(add);
      proof.addSubProofRup();
      proof.endSubProofContradiction();
    }
    atMostUnprocessedID = proof.logRedundancy(*logger, &atMost);
    //logger->protect.insert(atMostUnprocessedID);
    if (addToSolver) {
      atMost.proof.reset(atMostUnprocessedID);
      std::tie(atMostUnprocessedID, atMostID) = solver.addConstraint(atMost, Origin::COREGUIDED);
    }
  } else {
    assert(addToSolver);
    std::tie(atMostUnprocessedID, atMostID) = solver.addConstraint(atMost, Origin::COREGUIDED);
  }
  return atMostID;
}

template <typename SMALL, typename LARGE>
ID LazyVar<SMALL, LARGE>::addFinalAtMost() {
  return improveAtMost(1, true);
}

template <typename SMALL, typename LARGE>
bool LazyVar<SMALL, LARGE>::expand() {
  if (logger and not reified and upperBound < lastUpperBound) {
    improveAtMost(atMost.terms.back().c + upperBound - lastUpperBound, false);
    lastUpperBound = upperBound;
  }

  // add new variable
  long long newN = solver.getNbVars() + 1;
  solver.setNbVars(newN);
  lastVar = currentVar;
  addVar(newN);

  lastAtLeast = atLeastUnprocessedID;
  lastAtMost = atMostUnprocessedID;
  // log before adding, otherwise the solver might add new constraints in between
  logAtMost();
  logAtLeast();
  // add necessary lazy constraints
  if (addAtMost() == ID_Unsat || addAtLeast() == ID_Unsat ||
      addSymBreaking() == ID_Unsat) {
    assert(false);  // introducing a new variable, should not conflict
    return true;
  }

  // reformulate the objective
  reformObj->addLhs(cost, newN);
  if (logger) {
    if (reified) {
      sumReified.terms.emplace_back(-1, newN);
      ProofBuffer& proof = sumReified.proof;
      int j = coveredVars - 1;
      proof.addConstraint(j - 1, atLeastUnprocessedID, 1);
      proof << proofDiv(j);
      sumReifiedID = proof.logPolish(*logger);
    }
    else {
      atLeast.copyTo(sumReified);
      sumReifiedID = atLeastUnprocessedID;
      sumReified.proof.reset(sumReifiedID);
    }
  }

  return false;
}

template <typename SMALL, typename LARGE>
std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar<SMALL, LARGE>> lv) {
  o << lv->atLeast << "\n" << lv->atMost;
  return o;
}

// minimum coefficient over subset of vars
template <typename SMALL, typename LARGE>
SMALL minCoeff(const CePtr<ConstrExp<SMALL, LARGE>> ce, const std::vector<Var>& vars) {
  SMALL mult = 0;
  for (Var v : vars) {
    assert(ce->getLit(v) != 0);
    if (mult == 0) {
      mult = aux::abs(ce->coefs[v]);
    } else if (mult == 1) {
      break;
    } else {
      mult = std::min(mult, aux::abs(ce->coefs[v]));
    }
  }
  assert(mult > 0);
  return mult;
}

template <typename SMALL, typename LARGE>
ObjRewrite<SMALL, LARGE>::ObjRewrite(Env& env, Optimization<SMALL,LARGE>& opt, Ce32 cardCore)
    : opt(opt), logger(env.logger.get()), solver(*env.solver), cePools(*env.cePools), reformObj(opt.reformObj), cardCore(cardCore) {}

template <typename SMALL, typename LARGE>
bool ObjRewrite<SMALL, LARGE>::rewrite() {
  assert(cardCore->isCardinality());
  if (logger) {
    logger->logComment("Cardinality Core");
    coreID = cardCore->logProofLine();
  }
  cost = minCoeff(reformObj, cardCore->vars);

  // adjust the lower bound
  objLowerBound = opt.lower_bound;
  opt.lower_bound += cardCore->getDegree() * cost;

  bool eagerEncoding = options.cgEncoding.is("sum");

  upperBound = static_cast<int>(cardCore->vars.size());
  if (options.cgCoreUpper) {
    assert(opt.upper_bound - objLowerBound <= opt.normalizedUpperBound());
    // NOTE: integer division rounds down
    upperBound = static_cast<int>(std::min<LARGE>(upperBound, (opt.upper_bound-objLowerBound) / cost));
  }
  assert(upperBound >= 0);
  // lazy encoding makes sense with >= 2 variables
  eagerEncoding |= (upperBound - cardCore->getDegree() <= 1);

  // Actual replacement
  if (eagerEncoding) return rewriteEager();
  else return rewriteLazy();
}

template <typename SMALL, typename LARGE>
bool EagerVar<SMALL, LARGE>::addAtMost() {
  if (logger) {
    logger->logComment("New eager variable <=");
    cardCore->getProof().addWitness(newVars, 1);
    if (coreUBID != ID_Undef) {
      cardCore->getProof().addSubProof(coreUBID);
    }
  }
  std::tie(atMostUnprocessedID, atMostID) = solver.addConstraint(cardCore, Origin::COREGUIDED);
  return (atMostID == ID_Unsat);
}

template <typename SMALL, typename LARGE>
bool EagerVar<SMALL, LARGE>::addAtLeast() {
  if (logger) {
    logger->logComment("New eager variable =>");
    ID lastID = coreID;
    std::vector<ID> auxIDs;
    for (Var v : newVars) cardCore->addLhs(1, v);
    if (newVars.empty()) {
      cardCore->getProof().addWitness({});
      cardCore->getProof().addSubProof(lastID);
    }
    for (Var v : newVars) {
      cardCore->addLhs(-1, v);
      cardCore->getProof().addWitness(v, 0);
      cardCore->getProof().addSubProof(lastID);
      lastID = cardCore->logCG();
      auxIDs.push_back(lastID);
    }
    if (auxIDs.size() > 1) {
      auxIDs.pop_back();
      // TODO: create function in Logger
      logger->proof_out << "del id";
      for (ID id : auxIDs) {
        logger->proof_out << ' ' << id;
      }
      logger->proof_out << "\n";
    }
  }
  std::tie(atLeastUnprocessedID, atLeastID) = solver.addConstraint(cardCore, Origin::COREGUIDED);
  return (atLeastID == ID_Unsat);
}

std::vector<std::pair<Var, Var>> cycle(Var first, Var last) {
  std::vector<std::pair<Var, Var>> ret;
  for (Var v = first; v < last; ++v) ret.push_back({v+1, v});
  ret.push_back({first, last});
  return ret;
}

template <typename SMALL, typename LARGE>
bool EagerVar<SMALL, LARGE>::addSymmetryBreaking() {
  if (newVars.size() <= 1) return false;
  if (logger) {
    logger->logComment("Eager symmetry breaking");
  }
  for (Var v = newVars.front(); v < newVars.back(); ++v) {
    ID symUnprocessedID;
    ID symID;
    if (logger) {
      Ce32 aux = cePools.take32();
      aux->addLhs(1, v);
      aux->addLhs(1, -v - 1);
      aux->addRhs(1);
      aux->getProof().addWitness(cycle(newVars.front(), v+1));
      std::tie(symUnprocessedID, symID) = solver.addTempConstraint(aux, Origin::COREGUIDED);
    }
    else {
      std::tie(symUnprocessedID, symID) = solver.addConstraint(ConstrSimple32({{1, v}, {1, -v - 1}}, 1), Origin::COREGUIDED);
    }
    if (symID == ID_Unsat) return true;
  }
  return false;
}

template <typename SMALL, typename LARGE>
bool ObjRewrite<SMALL, LARGE>::rewriteEager() {
  EagerVar var(*this);
  return var.rewrite();
}

template <typename SMALL, typename LARGE>
EagerVar<SMALL, LARGE>::EagerVar(const ObjRewrite<SMALL, LARGE>& super) :
    opt(super.opt),
    logger(super.logger), solver(super.solver), cePools(super.cePools),
    reformObj(super.reformObj),
    cardCore(super.cardCore),
    coreID(super.coreID),
    cost(super.cost),
    upperBound(super.upperBound),
    coreUBID(ID_Undef) {}

template <typename SMALL, typename LARGE>
bool EagerVar<SMALL, LARGE>::rewrite() {
  if (logger and upperBound < static_cast<int>(cardCore->vars.size())) {
    coreUBID = opt.getCoreUB(cardCore, cost, upperBound);
  }

  // add auxiliary variables
  long long oldN = solver.getNbVars();
  long long numAux = upperBound - static_cast<int>(cardCore->getDegree());
  assert(numAux >= 0);
  long long newN = oldN + numAux;
  solver.setNbVars(newN);
  newVars.resize(numAux);
  iota(newVars.begin(), newVars.end(), oldN+1);

  // add constraints
  for (Var v : newVars) cardCore->addLhs(-1, v);
  cardCore->invert();
  if (addAtMost()) return true;
  cardCore->invert();
  if (addAtLeast()) return true;
  if (addSymmetryBreaking()) return true;

  // log objective reformulation
  if (logger) {
    cardCore->proof.reset(atLeastUnprocessedID);
    opt.refToOrigFixed->addUp(cardCore, cost);
    opt.refToOrig->addUp(cardCore, cost);
  }

  // reformulate the objective
  cardCore->invert();
  reformObj->addUp(cardCore, cost);
  assert(opt.lower_bound == -reformObj->getDegree());

  return false;
}

template <typename SMALL, typename LARGE>
bool ObjRewrite<SMALL, LARGE>::rewriteLazy() {
  // add auxiliary variable
  long long newN = solver.getNbVars() + 1;
  solver.setNbVars(newN);
  // add first lazy constraint
  opt.lazyVars.push_back(std::make_unique<LazyVar<SMALL, LARGE>>(*this, newN));
  LazyVar<SMALL, LARGE>& lv = *opt.lazyVars.back();
  lv.logAtMost();
  lv.logAtLeast();
  lv.addAtMost();
  lv.addAtLeast();
  if (logger) {
    lv.atLeast.copyTo(lv.sumReified);
    lv.sumReifiedID = ID(lv.atLeastUnprocessedID);
    lv.sumReified.proof.reset(lv.sumReifiedID);
    opt.refToOrig->addUp(lv.sumReified, cost);
  }
  // reformulate the objective
  cardCore->invert();
  reformObj->addUp(cardCore, cost);
  cardCore->invert();
  reformObj->addLhs(cost, newN);  // add only one variable for now
  assert(opt.lower_bound == -reformObj->getDegree());
  return false;
}

template struct ObjRewrite<int, long long>;
template struct ObjRewrite<long long, int128>;
template struct ObjRewrite<int128, int128>;
template struct ObjRewrite<int128, int256>;
template struct ObjRewrite<bigint, bigint>;
template struct LazyVar<int, long long>;
template struct LazyVar<long long, int128>;
template struct LazyVar<int128, int128>;
template struct LazyVar<int128, int256>;
template struct LazyVar<bigint, bigint>;

}  // namespace rs

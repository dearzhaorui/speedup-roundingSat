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

#include "optimize.hpp"

#include "ConstrExp.hpp"
#include "ConstrExpPool.hpp"
#include "Logger.hpp"
#include "Solver.hpp"
#include "objrewrite.hpp"

namespace rs {

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::Optimization(Env& env, CePtr<ConstrExp<SMALL, LARGE>> obj) :
    env(env),
    logger(env.logger.get()),
    solver(*env.solver),
    cePools(*env.cePools),
    origObj(obj),
    lastUpperBound(logger),
    lastUpperBoundUnprocessed(logger),
    lastLowerBound(logger),
    lastLowerBoundUnprocessed(logger),
    refToOrigFixedID(logger),
    refToOrigID(logger),
    objImproveID(logger),
    origID(logger) {
  assert(origObj->vars.size() > 0);
  // NOTE: -origObj->getDegree() keeps track of the offset of the reformulated objective (or after removing unit lits)
  lower_bound = -origObj->getDegree();
  upper_bound = origObj->absCoeffSum() - origObj->getRhs() + 1;

  reformObj = cePools.take<SMALL, LARGE>();
  reformObj->stopLogging();
  origObj->copyTo(reformObj);
  if (logger) {
    refToOrigFixed = cePools.take<SMALL, LARGE>();
    refToOrig = cePools.take<SMALL, LARGE>();
  }
  removeUnits();
}

template <typename SMALL, typename LARGE>
Optimization<SMALL, LARGE>::~Optimization() = default;

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::printObjBounds() {
  if (options.verbosity.get() == 0) return;
  std::cout << "c bounds ";
  if (solver.foundSolution()) {
    std::cout << bigint(upper_bound);  // TODO: remove bigint(...) hack
  } else {
    std::cout << "-";
  }
  std::cout << " >= " << bigint(lower_bound) << " @ " << stats.getTime() << "\n";  // TODO: remove bigint(...) hack
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::stopExpanding(size_t& i) {
  if (logger) {
    const LazyVar<SMALL, LARGE>& lv = *lazyVars[i];
    refToOrigFixed->addUp(lv.sumReified, lv.cost);
    // Already added to refToOrig, does not invalidate it
  }
  aux::swapErase(lazyVars, i--);  // fully expanded, no need to keep in memory
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::checkLazyVariables() {
  for (size_t i = 0; i < lazyVars.size(); ++i) {
    LazyVar<SMALL, LARGE>& lv = *lazyVars[i];

    // If a counting variable is fixed to 0 we can stop expanding
    // Symmetry breaking constraints would make all new counting variables 0
    if (isUnit(solver.getLevel(), -lv.currentVar)) {
      stopExpanding(i);
      continue;
    }

    // Only expand cores that appear in a new core
    if (reformObj->getLit(lv.currentVar) != 0) continue;

    if (options.cgCoreUpper) {
      assert(upper_bound - lv.objLowerBound <= normalizedUpperBound());
      LARGE cardCoreUpper = (upper_bound-lv.objLowerBound) / lv.cost;
      // NOTE: integer division rounds down
      if (cardCoreUpper < lv.upperBound)
      lv.setUpperBound(static_cast<int>(cardCoreUpper), lastUpperBoundUnprocessed);
    }

    // If the upper bound improves enough we can stop expanding
    // We improve the at most constraint first
    if (lv.remainingVars() == 0) {
        if (lv.addFinalAtMost() == ID_Unsat) return true;
      stopExpanding(i);
      continue;
    }

    refToOrigValid = false;
    if (lv.expand()) return true;

    if (lv.remainingVars() == 0) {
      stopExpanding(i);
    }
  }
  return false;
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::addLowerBound() {
  logObjective();
  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->addRhs(lower_bound);
  solver.dropExternal(lastLowerBound, true, true);
  std::tie(lastLowerBoundUnprocessed, lastLowerBound) = solver.addConstraint(aux, Origin::LOWERBOUND);
  if (lastLowerBound == ID_Unsat) return true;
  return false;
}

template <typename SMALL, typename LARGE>
std::pair<Ce32, int> Optimization<SMALL, LARGE>::reduceToCardinality(const CeSuper& core) {
  int bestNbBlocksRemoved = 0;
  CeSuper card = core->clone(cePools);
  if (options.cgReduction.is("clause")) {
    card->sortInDecreasingCoefOrder(
        [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
    card->simplifyToClause();
  } else if (options.cgReduction.is("minslack")) {
    card->sortInDecreasingCoefOrder(
        [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
    card->simplifyToMinLengthCardinality();
  } else {
    assert(options.cgReduction.is("bestbound"));
    CeSuper cloneCoefOrder = card->clone(cePools);
    cloneCoefOrder->sortInDecreasingCoefOrder();
    std::reverse(cloneCoefOrder->vars.begin(), cloneCoefOrder->vars.end());  // *IN*creasing coef order
    card->sort([&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) > aux::abs(reformObj->coefs[v2]); });
    CeSuper clone = card->clone(cePools);
    assert(clone->vars.size() > 0);
    LARGE bestLowerBound = 0;
    int bestNbVars = clone->vars.size();

    // find the optimum number of variables to weaken to
    int nbBlocksRemoved = 0;
    while (!clone->isTautology()) {
      int carddegree = cloneCoefOrder->getCardinalityDegreeWithZeroes();
      if (bestLowerBound < aux::abs(reformObj->coefs[clone->vars.back()]) * carddegree) {
        bestLowerBound = aux::abs(reformObj->coefs[clone->vars.back()]) * carddegree;
        bestNbVars = clone->vars.size();
        bestNbBlocksRemoved = nbBlocksRemoved;
      }
      SMALL currentObjCoef = aux::abs(reformObj->coefs[clone->vars.back()]);
      // weaken all lowest objective coefficient literals
      while (clone->vars.size() > 0 && currentObjCoef == aux::abs(reformObj->coefs[clone->vars.back()])) {
        ++nbBlocksRemoved;
        Var v = clone->vars.back();
        clone->weakenLast();
        cloneCoefOrder->weaken(v);
      }
    }

    // weaken to the optimum number of variables and generate cardinality constraint
    while ((int)card->vars.size() > bestNbVars) {
      card->weakenLast();
    }
    card->saturate();
    // sort in decreasing coef order to minimize number of auxiliary variables, but break ties so that *large*
    // objective coefficient literals are removed first, as the smallest objective coefficients are the ones that
    // will be eliminated from the objective function. Thanks Stephan!
    card->sortInDecreasingCoefOrder(
        [&](Var v1, Var v2) { return aux::abs(reformObj->coefs[v1]) < aux::abs(reformObj->coefs[v2]); });
    card->simplifyToCardinality(false);
  }

  Ce32 result = cePools.take32();
  card->copyTo(result);
  return {result, bestNbBlocksRemoved};
}

template <typename SMALL, typename LARGE>
std::tuple<LARGE, Ce32&, int> Optimization<SMALL, LARGE>::chooseCore(std::vector<std::pair<Ce32, int>>& cardCores) {
  LARGE bestLowerBound = -1;
  Ce32& bestCardCore = cardCores[0].first;
  int bestBlocksRemoved = 0;
  for (int i = 0; i < (int)cardCores.size(); ++i) {
    Ce32 cardCore = cardCores[i].first;
    assert(cardCore->hasNoZeroes());
    assert(cardCore->vars.size() > 0);
    SMALL lowestCoef = aux::abs(reformObj->coefs[cardCore->vars[0]]);
    for (Var v : cardCore->vars) {
      if (aux::abs(reformObj->coefs[v]) < lowestCoef) lowestCoef = aux::abs(reformObj->coefs[v]);
    }
    LARGE lowerBound = lowestCoef * cardCore->degree;
    if (i == 1) {
      stats.NOCOREBEST += lowerBound == bestLowerBound;
      stats.FIRSTCOREBEST += lowerBound < bestLowerBound;
      stats.DECCOREBEST += lowerBound > bestLowerBound;
    }
    if (lowerBound > bestLowerBound) {
      bestLowerBound = lowerBound;
      bestCardCore = cardCore;
      bestBlocksRemoved = cardCores[i].second;
    }
  }
  return {bestLowerBound, bestCardCore, bestBlocksRemoved};
}

template <typename SMALL, typename LARGE>
std::tuple<std::vector<std::pair<Ce32, int>>, bool> Optimization<SMALL, LARGE>::getCardCores(
    std::vector<CeSuper>& cores) {
  std::vector<std::pair<Ce32, int>> cardCores;
  for (CeSuper& core : cores) {
    assert(core);
    if (core->isTautology()) {
      continue;  // TODO: this only happens if we have an empty core
    }
    if (core->hasNegativeSlack(solver.getLevel())) {
      assert(solver.decisionLevel() == 0);  // TODO: this assert should be on the top of this function
      if (logger) core->logInconsistency(solver.getLevel(), solver.getPos(), stats);
      return {cardCores, true};
    }
    // figure out an appropriate core
    cardCores.push_back(reduceToCardinality(core));
  }
  return {cardCores, false};
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::removeUnits() {
  // take care of derived unit lits
  for (Var v : reformObj->vars) {
    if (isUnit(solver.getLevel(), v) || isUnit(solver.getLevel(), -v)) {
      assumps.remove(v);
      assumps.remove(-v);
    }
  }
  if (logger) {
    CePtr<ConstrExp<SMALL, LARGE>> delta = cePools.take<SMALL, LARGE>();
    std::vector<ID> hints;
    int nsimplified = 0;
    for (Var v : reformObj->vars) {
      Lit l = reformObj->getLit(v);
      if (l == 0) continue;
      SMALL c = reformObj->getCoef(l);
      delta->logIfUnitDelta(-l, c, solver.getLevel(), solver.getPos(), hints, nsimplified);
    }
    if (nsimplified > 0) {
      delta->proof.logDelta(*logger, delta, hints);
      refToOrigFixed->addUp(delta);
      refToOrig->addUp(delta);
    }
  }
  reformObj->removeUnitsAndZeroes(solver.getLevel(), solver.getPos(), false);
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::handleCores(std::vector<std::pair<Ce32, int>>& cardCores) {
  LARGE lowerBound;
  Ce32 cardCore;
  int blocksRemoved;
  std::tie(lowerBound, cardCore, blocksRemoved) = chooseCore(cardCores);

  stats.SINGLECORES += cardCores.size() == 1;
  stats.REMOVEDBLOCKS += blocksRemoved;
  stats.NCORECARDINALITIES += !cardCore->isClause();
  stats.COREDEGSUM += cardCore->getDegree();
  stats.CORESLACKSUM += cardCore->vars.size() - cardCore->getDegree();

  for (Var v : cardCore->vars) {
    assert(assumps.has(-cardCore->getLit(v)));
    assumps.remove(-cardCore->getLit(v));  // independent cores
    // TODO: maybe we should do weight aware core extraction
  }

  logObjective();
  return ObjRewrite(env, *this, cardCore).rewrite();
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::handleInconsistency(std::vector<CeSuper>& cores) {
  removeUnits();

  [[maybe_unused]] LARGE prev_lower = lower_bound;
  lower_bound = -reformObj->getDegree();

  std::vector<std::pair<Ce32, int>> cardCores;
  bool optimumFound;
  tie(cardCores, optimumFound) = getCardCores(cores);
  if (optimumFound) return true;

  if (cardCores.size() == 0) {
    // only violated unit assumptions were derived
    ++stats.UNITCORES;
    assert(lower_bound > prev_lower);
  } else {
    if (handleCores(cardCores)) return true;
  }

  if (checkLazyVariables()) return true;
  if (addLowerBound()) return true;
  if (!options.cgIndCores) assumps.clear();
  return false;
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::handleNewSolution(const std::vector<Lit>& sol) {
  [[maybe_unused]] LARGE prev_val = upper_bound;
  upper_bound = -origObj->getRhs();
  for (Var v : origObj->vars) upper_bound += origObj->coefs[v] * (int)(sol[v] > 0);
  assert(upper_bound < prev_val);

  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
  origObj->copyTo(aux);
  aux->invert();
  aux->addRhs(-upper_bound + 1);
  solver.dropExternal(lastUpperBound, true, true);
  std::tie(lastUpperBoundUnprocessed, lastUpperBound) = solver.addConstraint(aux, Origin::UPPERBOUND);
  objImproveValid = false;
  std::cout << "c BestSoFar: " << bigint(upper_bound) << ", nSolu= " << stats.NSOLS << std::endl;
  if (lastUpperBound == ID_Unsat) return true;
  return false;
}

template <typename SMALL, typename LARGE>
ID Optimization<SMALL, LARGE>::getObjToCore(Ce32 cardCore, SMALL cost, ID refToOrigID, LARGE lower_bound) {
  assert(logger);
  assert(refToOrigID != ID_Undef);
  logObjective();
  logger->logComment("Obj to Core");
  auto aux = cePools.take<SMALL,LARGE>();
  cardCore->copyTo(aux);
  aux->invert();
  aux->addUp(origObj, 1, cost);
  aux->addRhs(lower_bound);
  ProofBuffer& proof = aux->getProof();
  return proof.logImplied(*logger, aux, refToOrigID);
}


template <typename SMALL, typename LARGE>
ID Optimization<SMALL, LARGE>::getCoreUB(Ce32 cardCore, SMALL cost, int ub, ID objtoCoreID) {
  if (objtoCoreID == ID_Undef) objtoCoreID = getObjToCore(cardCore, cost, refToOrigID, lower_bound);
  logger->logComment("Core UB");
  ProofBuffer proof;
  proof.reset(objtoCoreID);
  proof.addClause(lastUpperBoundUnprocessed, 1);
  // We added -obj>=-(u-1), we subtract 1 from the RHS to get -obj>=-u
  proof.addVariable(1,1);
  proof.addVariable(1,-1);
  proof << proofDiv(cost);
  ID coreUBID = proof.logPolish(*logger);
  if (options.logDebug) {
    Ce32 aux = cardCore->cloneSameType(cePools);
    aux->invert();
    aux->addRhs(cardCore->getDegree()-ub);
    aux->logAssertEquals(coreUBID);
  }
  return coreUBID;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::logObjective(bool opt) {
  // (x) notation points to "Certified Core-Guided MaxSAT Solving"
  // https://doi.org/10.1007/978-3-031-38499-8_1
  if (not logger) return;

  // (2) Encodes origObj >= reformObj
  logger->logComment("Building origObj >= reformObj");
  refToOrigFixedID = refToOrigFixed->logProofLine();

  bool changed = not refToOrigValid;
  if (not refToOrigValid) {
    refToOrig = refToOrigFixed->cloneSameType(cePools);
    for (const auto& lv : lazyVars) {
      refToOrig->addUp(lv->sumReified, lv->cost);
    }
    refToOrigValid = true;
  }
  if (not refToOrig->proof.isTrivial()) changed = true;
  refToOrigID = refToOrig->logProofLine();

  if (not opt and not changed) return;

  objImproveValid = false;
  if (opt) logUpperBound();

  logger->logComment("Reformulated objective");
  // Orig = Ref + (2)
  CePtr<ConstrExp<SMALL, LARGE>> aux = cePools.take<SMALL, LARGE>();
  reformObj->copyTo(aux);
  aux->addRhs(lower_bound);
  ID refID;
  if (opt) refID = aux->proof.logRup(*logger, aux);
  else refID = aux->proof.logTrivial(*logger, aux);
  aux->addUp(refToOrig);
  origID = aux->logProofLine();
  origObj->getProof().reset(origID);
  logger->unused.push_back(refID);
  if (options.logDebug) {
    logger->logComment("Original objective");
    origObj->addRhs(lower_bound);
    origObj->logAssertEquals(origID);
    origObj->addRhs(-lower_bound);
  }

  logger->gc();
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::logUpperBound() {
  if (not logger) return;
  if (lastUpperBoundUnprocessed == ID_Undef) return;
  logObjective();
  if (objImproveValid) return;
  // (3b) Objective improving constraint
  CePtr<ConstrExp<SMALL, LARGE>> aux = origObj->cloneSameType(cePools);
  aux->invert();
  aux->addRhs(1 - upper_bound);
  aux->proof.reset(lastUpperBoundUnprocessed);
  // (6) = (2) + (3b) proves optimality or hardening
  aux->addUp(refToOrig);
  objImproveID = aux->logProofLine();
  objImproveValid = true;
}

template <typename SMALL, typename LARGE>
bool Optimization<SMALL, LARGE>::harden() {
  LARGE diff = upper_bound - lower_bound;
  for (Var v : reformObj->vars) {
    if (aux::abs(reformObj->coefs[v]) > diff) {
      ConstrSimple32 c({{1, -reformObj->getLit(v)}}, 1, Origin::HARDENEDBOUND);
      if (logger) {
        logUpperBound();
        c.proof.logRup(*logger, &c, {objImproveID});
      }
      if (solver.addConstraint(c, Origin::HARDENEDBOUND).second == ID_Unsat) return true;
    }
  }
  return false;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::logOptimum() {
  assert(logger);
    logObjective(true);
    if (lower_bound != upper_bound) {
      origObj->addRhs(upper_bound);
      origObj->logRup();
      origObj->addRhs(-upper_bound);
    }
  }

template <typename SMALL, typename LARGE>
OptState Optimization<SMALL, LARGE>::makeAnswer() {
  if (solver.foundSolution()) {
    if (logger) logOptimum();
    return OptState::OPT;
  }
  return OptState::UNSAT;
}

template <typename SMALL, typename LARGE>
SMALL& Optimization<SMALL, LARGE>::setStratificationThreshold(SMALL& coeflim) {
  // find a new coeflim
  reformObj->sortInDecreasingCoefOrder();
  int numLargerCoefs = 0;
  int numLargerUniqueCoefs = 0;
  SMALL prevCoef = -1;
  for (Var v : reformObj->vars) {
    SMALL coef = aux::abs(reformObj->coefs[v]);
    ++numLargerCoefs;
    numLargerUniqueCoefs += prevCoef != coef;
    prevCoef = coef;
    if (coeflim > coef && numLargerCoefs / numLargerUniqueCoefs > 1.25) return coeflim = coef;
  }
  return coeflim = 0;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::setAssumptions(SMALL& coeflim, CoefLimStatus& coefLimFlag) {
  // use core-guided step by setting assumptions
  reformObj->removeZeroes();
  if (coeflim > 0 && coefLimFlag == CoefLimStatus::REFINE) {
    setStratificationThreshold(coeflim);
  }
  std::vector<Term<double>> litcoefs;  // using double will lead to faster sort than bigint
  litcoefs.reserve(reformObj->vars.size());
  for (Var v : reformObj->vars) {
    assert(reformObj->getLit(v) != 0);
    SMALL cf = aux::abs(reformObj->coefs[v]);
    if (cf >= coeflim) litcoefs.emplace_back(static_cast<double>(cf), v);
  }
  std::sort(litcoefs.begin(), litcoefs.end(), [](const Term<double>& t1, const Term<double>& t2) {
    return t1.c > t2.c || (t1.l < t2.l && t1.c == t2.c);
  });
  for (const Term<double>& t : litcoefs) assumps.add(-reformObj->getLit(t.l));
  coefLimFlag = CoefLimStatus::ENCOUNTEREDSAT;
}

template <typename SMALL, typename LARGE>
void Optimization<SMALL, LARGE>::initExecInfoWriterReader() {
  std::cout << "c options: --time-limit= " << options.time_limit.get() << ", --prop-counting= " << options.propCounting.get() << std::endl;
  std::cout << "c benchmark: " << options.formulaName << std::endl;
  std::cout << "c writeFile? " << bool(options.writeFile) << ", readFile? " << bool(options.readFile) << ", execFile: " << options.execFile.get() << std::endl;

  assert((bool(options.writeFile) != bool(options.readFile) and !options.execFile.get().empty()) or (!options.writeFile and !options.readFile));
  solver.setWriteOrReadInfo(bool(options.writeFile), bool(options.readFile));
  
  if (!options.readFile) {std::cout << "c this version only supports reading from log file!" << std::endl; exit(0);}
  assert(options.readFile);
  
  if (options.writeFile) {
    std::ofstream* einfo = new std::ofstream(options.execFile.get());
    solver.setExecutionFileName(einfo);
  }
  else if (options.readFile) {
    solver.initLogReader(options.execFile.get());
    solver.logReader->readUntilNextCleanup();
    if (!solver.confCoreLem.empty()) {solver.nextConfForCoreLem = solver.confCoreLem.front(); solver.confCoreLem.pop();}
  }
  else std::cout << "c only run RoundingSAT" << std::endl;
}

template <typename SMALL, typename LARGE>
OptState Optimization<SMALL, LARGE>::optimize() {
  initExecInfoWriterReader();
  
  size_t upper_time = 0, lower_time = 0;
  SolveState reply = SolveState::SAT;
  SMALL coeflim = options.cgStrat ? reformObj->getLargestCoef() : 0;

  CoefLimStatus coefLimFlag = CoefLimStatus::REFINE;
  while (true) {
    size_t current_time = stats.getDetTime();
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get()) {
      throw timeoutInterrupt;
    }
    //if (reply != SolveState::INPROCESSED && reply != SolveState::RESTARTED) {
      //printObjBounds();
    //}
    
    if (solver.assumpRefs.empty()) {
      std::cout << "\nSolving is finished because time limit reached....\n" << std::flush;
      assert(solver.lemmas.empty() and solver.allDecisions.empty() and solver.coreCes.empty() and solver.direct0s.empty() and solver.confCoreLem.empty());
      printObjBounds();
      if (solver.foundSolution()) {
        return OptState::SAT;
      }
      return OptState::UNKNOWN;
    }
    
    char reform = solver.assumpRefs.front();
    solver.assumpRefs.pop();
    
    if (reform) setAssumptions(coeflim, coefLimFlag);
      
    assert(upper_bound > lower_bound);
    SolveAnswer out = aux::timeCall<SolveAnswer>(
        [&] {
          solver.setAssumptions(assumps);
          return solver.solve_read();
        },
        assumps.isEmpty() ? stats.SOLVETIME : stats.SOLVETIMECG);
    reply = out.state;
    if (reply == SolveState::RESTARTED) continue;
    if (reply == SolveState::UNSAT) {
      printObjBounds();
      return makeAnswer();
    }
    if (assumps.isEmpty()) {
      upper_time += stats.getDetTime() - current_time;
    } else {
      lower_time += stats.getDetTime() - current_time;
    }
    if (reply == SolveState::SAT) {
      assumps.clear();
      assert(solver.foundSolution());
      ++stats.NSOLS;
      if (handleNewSolution(out.solution)) return makeAnswer();
      if (harden()) return makeAnswer();
      if (coefLimFlag == CoefLimStatus::ENCOUNTEREDSAT) coefLimFlag = CoefLimStatus::REFINE;
    } else if (reply == SolveState::INCONSISTENT) {
      assert(solver.decisionLevel() == 0);
      assert(!options.optMode.is("linear"));
      ++stats.NCORES;
      if (handleInconsistency(out.cores)) return makeAnswer();
      if (harden()) return makeAnswer();
      coefLimFlag = CoefLimStatus::START;
    } else if (reply == SolveState::INTERRUPTED) {
      assert(solver.read);
      std::cout << "\nSolving is finished....\n" << std::flush;
      assert(solver.lemmas.empty() and solver.allDecisions.empty() and solver.coreCes.empty() and solver.confCoreLem.empty() and solver.assumpRefs.empty() and solver.direct0s.empty());
      printObjBounds();
      if (solver.foundSolution()) {
        return OptState::SAT;
      }
      return OptState::UNKNOWN;
    } else {
      assert(reply == SolveState::INPROCESSED);  // keep looping
      // coefLimFlag = CoefLimStatus::REFINE;
      // NOTE: above avoids long non-terminating solve calls due to insufficient assumptions
      assumps.clear();
    }
    if (lower_bound >= upper_bound) {
      printObjBounds();
      return makeAnswer();
    }
  }
}

template class Optimization<int, long long>;
template class Optimization<long long, int128>;
template class Optimization<int128, int128>;
template class Optimization<int128, int256>;
template class Optimization<bigint, bigint>;

}  // namespace rs

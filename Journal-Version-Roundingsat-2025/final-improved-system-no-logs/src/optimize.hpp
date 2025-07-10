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
#include <tuple>

#include "IntSet.hpp"
#include "auxlog.hpp"
#include "typedefs.hpp"

namespace rs {

class ConstrExpPools;
class Env;
class Logger;
class Solver;

template <typename SMALL, typename LARGE>
struct ObjRewrite;
template <typename SMALL, typename LARGE>
struct LazyVar;
template <typename SMALL, typename LARGE>
struct EagerVar;

enum class OptState { SAT, UNSAT, OPT, UNKNOWN };

class IOptimization {
public:
  virtual bigint getUpperBound() = 0;
  virtual bigint getLowerBound() = 0;
  virtual OptState optimize() = 0;
  virtual ~IOptimization() {};
};

template <typename SMALL, typename LARGE>
class Optimization : public IOptimization {
  Env& env;
  Logger* logger;
  Solver& solver;
  ConstrExpPools& cePools;

  // original objective
  const CePtr<ConstrExp<SMALL, LARGE>> origObj;
  // reformulated objective
  // coeffs bounded by origObj, hence SMALL/LARGE is enough
  CePtr<ConstrExp<SMALL, LARGE>> reformObj;
  // fixed part of the reformObj >= origObj constraint
  // i.e. consisting only of fully expanded cores
  // the part consisting of partially expanded cores needs to be rederived
  CePtr<ConstrExp<SMALL, LARGE>> refToOrigFixed;
  CePtr<ConstrExp<SMALL, LARGE>> refToOrig;
  bool refToOrigValid = true;
  bool objImproveValid = true;

  LARGE lower_bound;
  LARGE upper_bound;
  autoID lastUpperBound;
  autoID lastUpperBoundUnprocessed;
  autoID lastLowerBound;
  autoID lastLowerBoundUnprocessed;

  // partially expanded cores
  std::vector<std::unique_ptr<LazyVar<SMALL, LARGE>>> lazyVars;
  IntSet assumps;

  autoID refToOrigFixedID;
  autoID refToOrigID;
  autoID objImproveID;
  autoID origID;

  enum class CoefLimStatus { START, ENCOUNTEREDSAT, REFINE };
  SMALL& setStratificationThreshold(SMALL& coeflim);
  void setAssumptions(SMALL& coeflim, CoefLimStatus& coefLimFlag);
  /**
   * @brief
   *
   * @param core
   * @return std::pair<Ce32, int>
   * @todo The performance of this function could be improved
   */
  std::pair<Ce32, int> reduceToCardinality(const CeSuper& core);
  /**
   * @brief Choose core with best lower bound increase.
   *
   * @param cardCores
   * @return std::tuple<LARGE, Ce32&, int>
   */
  std::tuple<LARGE, Ce32&, int> chooseCore(std::vector<std::pair<Ce32, int>>& cardCores);
  std::tuple<std::vector<std::pair<Ce32, int>>, bool> getCardCores(std::vector<CeSuper>& cores);
  void removeUnits();
  bool handleCores(std::vector<std::pair<Ce32, int>>& cardCores);
  void stopExpanding(size_t& i);
  bool checkLazyVariables();

  ID getObjToCore(Ce32 cardCore, SMALL cost, ID refToOrigID, LARGE lower_bound);
  ID getCoreUB(Ce32 cardCore, SMALL cost, int ub, ID objtoCoreID = ID_Undef);
  void logUpperBound();
  void logObjective(bool opt=false);
  void logOptimum();
  OptState makeAnswer();

 public:
  Optimization(Env& env, CePtr<ConstrExp<SMALL, LARGE>> obj);
  Optimization(const Optimization&) = delete;
  ~Optimization();

  LARGE normalizedLowerBound() { return lower_bound + origObj->getDegree(); }
  LARGE normalizedUpperBound() { return upper_bound + origObj->getDegree(); }

  void printObjBounds();
  bigint getLowerBound() { return bigint(lower_bound); }
  bigint getUpperBound() { return bigint(upper_bound); }

  bool addLowerBound();

  bool handleInconsistency(std::vector<CeSuper>& cores);
  bool handleNewSolution(const std::vector<Lit>& sol);
  bool harden();

  OptState optimize();

  friend ObjRewrite<SMALL, LARGE>;
  friend EagerVar<SMALL, LARGE>;
  friend LazyVar<SMALL, LARGE>;
};

}  // namespace rs

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

#include "ConstrExp.hpp"
#include "optimize.hpp"

namespace rs {

// Replace mult*cardCore by sum(new variables) in the objective
template <typename SMALL, typename LARGE>
struct ObjRewrite {
  Optimization<SMALL, LARGE>& opt;
  Logger* logger;
  Solver& solver;
  ConstrExpPools& cePools;
  CePtr<ConstrExp<SMALL, LARGE>> reformObj;
  Ce32 cardCore;
  ID coreID;
  SMALL cost;
  LARGE objLowerBound;
  int upperBound;

  ObjRewrite(Env& env, Optimization<SMALL, LARGE>& opt, Ce32 cardCore);
  bool rewrite();
  bool rewriteEager();
  bool rewriteLazy();
};

template <typename SMALL, typename LARGE>
struct EagerVar {
  Optimization<SMALL, LARGE>& opt;
  Logger* logger;
  Solver& solver;
  ConstrExpPools& cePools;
  CePtr<ConstrExp<SMALL, LARGE>> reformObj;
  Ce32 cardCore;
  ID coreID;
  SMALL cost;
  int upperBound;
  std::vector<Var> newVars;
  ID coreUBID;
  ID atMostUnprocessedID;
  ID atMostID;
  ID atLeastUnprocessedID;
  ID atLeastID;

  EagerVar(const ObjRewrite<SMALL, LARGE>& super);
  bool rewrite();
  bool addAtMost();
  bool addAtLeast();
  bool addSymmetryBreaking();
};

// Represents a core that is not yet fully expanded
template <typename SMALL, typename LARGE>
struct LazyVar {
  Optimization<SMALL, LARGE>& opt;
  Logger* logger;
  Solver& solver;
  ConstrExpPools& cePools;
  CePtr<ConstrExp<SMALL, LARGE>> reformObj;
  SMALL cost;
  // Lower bound at the time this core was found, not updated
  LARGE objLowerBound;
  LARGE newLowerBound;
  int upperBound;
  int lastUpperBound;

  // Core LB, needed to derive at least
  ConstrSimple32 cardCore;
  autoID coreID;
  // Core UB, needed to derive at most
  autoID coreUBID;

  // orig >= reform at the time this core was found, not updated
  autoID refToOrigID;
  // Remove literals outside support from the objective
  autoID objToCoreID;

  int coveredVars;  // i
  Var currentVar;
  Var lastVar;

  // Standard reification would encode yi <-> [core >= i]
  // However, we already know that (core) >= deg
  // Hence we start at i = deg+1 and we have the stronger
  // atLeast: yi -> [core >= i + deg], i.e. i-deg ~yi + (core) >= i
  // atMost:  [core >= i] -> yi, i.e. |core|-i+1 yi - (core) >= -i + 1
  // Note that in literal normal form this would be
  // |core|-i+1 yi + ~(core) >= |core| - i + 1
  //
  // If not reified then we have
  // atLeast: X >= k + y1 + ... + yi
  // atMost:  k + y1 + ... + yi-1 + (1+n-k-i)yi >= X
  ConstrSimple32 atLeast;
  autoID atLeastUnprocessedID;
  autoID atLeastID;
  ID lastAtLeast;
  ConstrSimple32 atMost;
  autoID atMostUnprocessedID;
  autoID atMostID;
  ID lastAtMost;

  // (core) >= deg + y1 + ... + yi
  // equiv. (core) + ~y1 + ... + ~yi >= deg + i
  ConstrSimple32 sumReified;
  autoID sumReifiedID;

  bool reified;

  LazyVar(const ObjRewrite<SMALL, LARGE>& super, Var startVar);
  ~LazyVar();

  void addVar(Var v);
  void logAtLeast();
  void logAtMost();
  ID addAtLeast();
  ID addAtMost();
  ID addSymBreaking() const;
  ID addFinalAtMost();
  ID improveAtMost(int newc, bool addToSolver);
  int remainingVars() const;
  void setUpperBound(int cardUpperBound, ID UBID);

  bool expand();
};

template <typename SMALL, typename LARGE>
std::ostream& operator<<(std::ostream& o, const std::shared_ptr<LazyVar<SMALL, LARGE>> lv);

}  // namespace rs

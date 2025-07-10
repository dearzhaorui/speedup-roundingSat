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

#include <sstream>
#include <span>
#include "auxiliary.hpp"
#include "auxlog.hpp"
#include "typedefs.hpp"

namespace rs {

class autoID;
class Logger;

// Syntactic sugar
template <typename T>
struct proofMult {
  const T& m;
  proofMult(const T& mult) : m(mult) {}
};
template <typename T>
std::ostream& operator<<(std::ostream& os, const proofMult<T>& mult) {
  if (mult.m != 1) os << mult.m << " * ";
  return os;
}

// Syntactic sugar
template <typename T>
struct proofDiv {
  const T& d;
  proofDiv(const T& div) : d(div) {}
};
template <typename T>
std::ostream& operator<<(std::ostream& os, const proofDiv<T>& div) {
  return os << div.d << " d ";
}

// Syntactic sugar
struct proofLit {
  Lit l;
  proofLit(Lit l) : l(l) {}
};
inline std::ostream& operator<<(std::ostream& o, proofLit l) { return o << (l.l < 0 ? " ~x" : " x") << toVar(l.l); }

enum class ProofRule { POLISH, REDUNDANCY };

// Tree of operations used to derive a constraint,
// represented in reverse Polish notation
struct ProofBuffer {
  std::stringstream buffer;
  enum ProofRule rule = ProofRule::POLISH;
  size_t pad = 0;
  std::vector<autoID> tempids; // temporary IDs used for the current Polish line; can be deleted after logging this line
  
  operator std::ostream&() { return buffer; }

  bool isTrivial() const;

  void reset();
  void reset(ID proofId);
  void resetRelative(long long relId);
  ProofBuffer() = default;
  ProofBuffer(const ProofBuffer& other);
  ProofBuffer& operator = (const ProofBuffer& other);

  template <typename SMALL>
  void addVariable(Var v, const SMALL& m) {
    if (m > 0)
      buffer << "x" << v << " " << proofMult(m) << "+ ";
    else
      buffer << "~x" << v << " " << proofMult(-m) << "+ ";
  }
  template <typename SMALL>
  void addLiteral(Lit l, const SMALL& c) {
    buffer << proofLit(l) << " " << proofMult(c) << "+ ";
  }
  void addConstraint(ID id) {
    buffer << id << " + ";
  }
  template <typename SMALL>
  void addClause(ID id, const SMALL& c) {
    buffer << id << " " << proofMult(c) << "+ ";
  }
  template <typename SMALL>
  void addConstraint(const SMALL& thismult, ID id, const SMALL& c) {
    buffer << proofMult(thismult) << " " << id << " " << proofMult(c) << "+ ";
  }
  template <typename SMALL>
  void addConstraint(const SMALL& thismult, const ProofBuffer& other, const SMALL& othermult) {
    buffer << proofMult(thismult) << other.buffer.view() << proofMult(othermult) << "+ ";
    tempids.insert(tempids.end(), other.tempids.begin(), other.tempids.end());
  }
  template <typename SMALL>
  void addConstraintRelID(const SMALL& thismult, long long relID, const SMALL& c) {
  assert(relID < 0);
    buffer << proofMult(thismult) << " " << relID << " " << proofMult(c) << "+ ";
  }
  template <typename SMALL>
  void divide(const SMALL& div) { buffer << proofDiv(div); }
  void weakenVariable(Var v) { buffer << "x" << v << " w "; }
  void weakenLiteral(Lit l) { weakenVariable(toVar(l)); }
  void saturate() { buffer << "s "; }
  void replaceFirst(ID id);
  void popFirst();
  void addWitness(Var v, int sign);
  void addWitness(const std::span<const Var>& vars, int sign);
  void addWitness(const std::span<const std::pair<Var,Var>>& permutation);
  void addSubProof(ID id);
  void beginSubProof();
  void beginGoal();
  void addSubProofStepRedundance(const ProofBuffer& other, CeSuper ce);
  void addSubProofStep(const ProofBuffer& other);
  void addSubProofRup();
  void endGoal();
  void endSubProof();
  void endSubProofContradiction();

  ID logPolish(Logger& logger);
  template<typename CPtr>
  ID logRedundancy(Logger& logger, CPtr ce);
  void addSubProofStepRup(CeSuper ce);
  ID logRup(Logger& logger, CeSuper ce, const std::vector<ID>& hintVec = {});
  ID logRup(Logger& logger, ConstrSimple32* ce, const std::vector<ID>& hintVec = {});
  ID logImplied(Logger& logger, CeSuper ce, ID hint = ID_Undef);
  ID logImplied(Logger& logger, ConstrSimple32* ce, ID hint = ID_Undef);
  ID logUnit(Logger& logger, Lit p, const std::vector<ID>& hintVec = {});
  ID logTrivial(Logger& logger, CeSuper ce);
  ID logAssumption(Logger& logger, CeSuper ce);
  template<typename CPtr>
  ID logExternal(const std::string& rule, Logger& logger, CPtr ce, const std::vector<ID>& hintVec = {});
  template <typename SMALL, typename LARGE>
  ID logDelta(Logger& logger, CePtr<ConstrExp<SMALL, LARGE>> &delta, std::vector<ID> &hints);
  template <typename SMALL, typename LARGE>
  void logDeltaAndAdd(Logger& logger, CePtr<ConstrExp<SMALL, LARGE>> &delta, std::vector<ID> &hints, int nsimplified);
  ID log(Logger& logger, CeSuper ce);
};

}  // namespace rs

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

#include "ProofBuffer.hpp"

#include "ConstrExp.hpp"
#include "Logger.hpp"

namespace rs {

bool ProofBuffer::isTrivial() const {
  auto str = buffer.view();
  assert(str.back() == ' ');
  return str.find(' ') + 1 == str.length();
}

void ProofBuffer::reset() {
  buffer.clear();
  buffer.str(std::string());
  rule = ProofRule::POLISH;
  pad = 0;
  tempids.clear();
}

void ProofBuffer::reset(ID proofID) {
  assert(proofID != ID_Undef);
  assert(proofID != ID_Unsat);
  reset();
  buffer << proofID << " ";
}

void ProofBuffer::resetRelative(long long relID) {
  assert(relID < 0);
  reset();
  buffer << relID << " ";
}

ProofBuffer::ProofBuffer(const ProofBuffer& other) {
  *this = other;
}


ProofBuffer& ProofBuffer::operator = (const ProofBuffer& other) {
  if (this == &other) return *this;
  reset();
  buffer << other.buffer.str();
  rule = other.rule;
  pad = other.pad;
  tempids = other.tempids;
  return *this;
}

void ProofBuffer::replaceFirst(ID id) {
  assert(rule == ProofRule::POLISH);
  std::string tail(buffer.view().substr(buffer.view().find(' ') + 1));
  reset(id);
  buffer << tail;
}

void ProofBuffer::popFirst() {
  assert(rule == ProofRule::POLISH);
  std::string tail(buffer.view().substr(buffer.view().find(' ') + 1));
  buffer.clear();
  buffer.str(tail);
}

void ProofBuffer::addWitness(Var v, int sign) {
  addWitness(std::span<Var>(&v,1), sign);
}

void ProofBuffer::addWitness(const std::span<const Var>& vars, int sign) {
  rule = ProofRule::REDUNDANCY;
  buffer.clear();
  buffer.str(std::string());
  pad = 0;
  for (Var v : vars) buffer << " x" << v << " -> " << sign;
  buffer << " ;";
}

void ProofBuffer::addWitness(const std::span<const std::pair<Var,Var>>& permutation) {
  rule = ProofRule::REDUNDANCY;
  buffer.clear();
  buffer.str(std::string());
  pad = 0;
  for (auto [u,v] : permutation) buffer << " x" << u << " -> x" << v;
  buffer << " ;";
}

void ProofBuffer::addSubProof(ID id) {
  assert(id != ID_Undef);
  assert(id != ID_Unsat);
  beginSubProof();
  beginGoal();
  ProofBuffer add;
  add.resetRelative(-1);
  add.addConstraint(id);
  addSubProofStep(add);
  endGoal();
  endSubProof();
}

void ProofBuffer::beginSubProof() {
  assert(rule == ProofRule::REDUNDANCY);
  buffer << " begin\n";
}

void ProofBuffer::beginGoal() {
  buffer << "proofgoal #1\n";
  ++pad;
}

void ProofBuffer::addSubProofStep(const ProofBuffer& other) {
  buffer << "pol " << other.buffer.view() << "\n";
  ++pad;
}

void ProofBuffer::addSubProofStepRup(CeSuper ce) {
  buffer << "rup ";
  ce->toStreamAsOPB(buffer);
  buffer << ID_Undef << "\n";
  ++pad;
}

void ProofBuffer::addSubProofStepRedundance(const ProofBuffer& other, CeSuper ce) {
  buffer << "red ";
  ce->toStreamAsOPB(buffer);
  buffer << other.buffer.view() << "\n";
  pad += other.pad;
  ++pad;
}

void ProofBuffer::addSubProofRup() {
  buffer << "rup >= 1 ;\n";
  ++pad;
}

void ProofBuffer::endGoal() {
  buffer << "end -1\n";
}

void ProofBuffer::endSubProof() {
  assert(rule == ProofRule::REDUNDANCY);
  buffer << "end";
  ++pad;
}

void ProofBuffer::endSubProofContradiction() {
  assert(rule == ProofRule::REDUNDANCY);
  buffer << "end -1";
  ++pad;
}

ID ProofBuffer::logPolish(Logger& logger) {
  ID id;
  if (isTrivial()) {  // line is just one id, don't print it
    buffer >> id;
    buffer.seekg(0);
  } else {  // non-trivial line
    id = ++logger.last_proofID;
    logger.proof_out << "p " << buffer.view() << "\n";
    reset(id);
  }
  return id;
}

template<typename CPtr>
ID ProofBuffer::logRedundancy(Logger& logger, CPtr ce) {
  logger.proof_out << "red ";
  ce->toStreamAsOPB(logger.proof_out);
  logger.proof_out << buffer.view() << "\n";
  logger.last_proofID += pad;
  ID id = ++logger.last_proofID;
  reset(id);  // ensure consistent proofBuffer
  return id;
}
template ID ProofBuffer::logRedundancy<CeSuper>(Logger&, CeSuper);
template ID ProofBuffer::logRedundancy<ConstrSimple32*>(Logger&, ConstrSimple32*);

template<typename CPtr>
ID ProofBuffer::logExternal(const std::string& rule, Logger& logger, CPtr ce, const std::vector<ID>& hintVec) {
  logger.proof_out << rule;
  ce->toStreamAsOPB(logger.proof_out);
  for (auto hint: hintVec)
    logger.proof_out << " " << hint;
  logger.proof_out << "\n";
  ID id = ++logger.last_proofID;
  reset(id);  // ensure consistent proofBuffer
  return id;
}
template ID ProofBuffer::logExternal<CeSuper>(const std::string&, Logger&, CeSuper, const std::vector<ID>&);
template ID ProofBuffer::logExternal<ConstrSimple32*>(const std::string&, Logger&, ConstrSimple32*, const std::vector<ID>&);

ID ProofBuffer::logRup(Logger& logger, CeSuper ce, const std::vector<ID>& hintVec) { return logExternal("rup ", logger, ce, hintVec); }
ID ProofBuffer::logRup(Logger& logger, ConstrSimple32* ce, const std::vector<ID>& hintVec) { return logExternal("rup ", logger, ce, hintVec); }

ID ProofBuffer::logImplied(Logger& logger, CeSuper ce, ID hint) {
  if (hint != ID_Undef) return logExternal("ia ", logger, ce, {hint});
  return logExternal("ia ", logger, ce, {});
}
ID ProofBuffer::logImplied(Logger& logger, ConstrSimple32* ce, ID hint)  {
  if (hint != ID_Undef) return logExternal("ia ", logger, ce, {hint});
  return logExternal("ia ", logger, ce, {});
}

ID ProofBuffer::logTrivial(Logger& logger, CeSuper ce) { return logImplied(logger, ce, logger.ID_Trivial); }

ID ProofBuffer::logUnit(Logger& logger, Lit p, const std::vector<ID>& hintVec) {
  ConstrSimple32 ce({{1,p}}, 1);
  ID id = logRup(logger, &ce, hintVec);
  logger.unitIDs.push_back(id);
  logger.protect.insert(id);
  return id;
}

template <typename SMALL, typename LARGE>
ID ProofBuffer::logDelta(Logger& logger, CePtr<ConstrExp<SMALL, LARGE>> &delta, std::vector<ID> &hints) {
  if (hints.size() == 0)
    hints.push_back(logger.ID_Trivial);
  ID id = logRup(logger, delta, hints);
  tempids.emplace_back(&logger, id);
  return id;
}
template ID ProofBuffer::logDelta(Logger&, CePtr<ConstrExp<int, long long>> &, std::vector<ID> &);
template ID ProofBuffer::logDelta(Logger&, CePtr<ConstrExp<long long, int128>> &, std::vector<ID> &);
template ID ProofBuffer::logDelta(Logger&, CePtr<ConstrExp<int128, int128>> &, std::vector<ID> &);
template ID ProofBuffer::logDelta(Logger&, CePtr<ConstrExp<int128, int256>> &, std::vector<ID> &);
template ID ProofBuffer::logDelta(Logger&, CePtr<ConstrExp<bigint, bigint>> &, std::vector<ID> &);

template <typename SMALL, typename LARGE>
void ProofBuffer::logDeltaAndAdd(Logger& logger, CePtr<ConstrExp<SMALL, LARGE>> &delta, std::vector<ID> &hints, int nsimplified) {
  if (nsimplified > 1) {
    delta->proof.logDelta(logger, delta, hints);
    addConstraint(1, delta->proof, 1);
  } else if (nsimplified == 1 && hints.size() == 0) {
      // delta consists of adding a single trivial constraint (so directly add it rather than logging an additional constraint)
    Lit l = delta->getLit(delta->vars[0]);
    SMALL c = delta->getCoef(l);
    addLiteral(l, c);
  } else if (nsimplified == 1 && hints.size() == 1) {
      // delta consists of adding a single unit (so directly add it rather than logging an additional constraint)
    Lit l = delta->getLit(delta->vars[0]);
    SMALL c = delta->getCoef(l);
    addConstraint(static_cast<SMALL>(1), hints[0], c);
  }
}
template void ProofBuffer::logDeltaAndAdd(Logger&, CePtr<ConstrExp<int, long long>> &, std::vector<ID> &, int);
template void ProofBuffer::logDeltaAndAdd(Logger&, CePtr<ConstrExp<long long, int128>> &, std::vector<ID> &, int);
template void ProofBuffer::logDeltaAndAdd(Logger&, CePtr<ConstrExp<int128, int128>> &, std::vector<ID> &, int);
template void ProofBuffer::logDeltaAndAdd(Logger&, CePtr<ConstrExp<int128, int256>> &, std::vector<ID> &, int);
template void ProofBuffer::logDeltaAndAdd(Logger&, CePtr<ConstrExp<bigint, bigint>> &, std::vector<ID> &, int);

ID ProofBuffer::logAssumption(Logger& logger, CeSuper ce) { return logExternal("a ", logger, ce); }

ID ProofBuffer::log(Logger& logger, CeSuper ce) {
  if (rule == ProofRule::POLISH)
    return logPolish(logger);
  else
    return logRedundancy(logger, ce);
}

}  // namespace rs

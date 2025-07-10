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

#include "Logger.hpp"

#include <ranges>

#include "ProofBuffer.hpp"
#include "auxlog.hpp"

namespace rs {

Logger::Logger(std::ostream& proof_out) : proof_out(proof_out) {}

void Logger::init(unsigned int num_constraints) {
  proof_out << "pseudo-Boolean proof version 2.0\n";
  proof_out << "f " << num_constraints << "\n";
  last_proofID = num_constraints;
  // Dummy constraint for easier proof logging.
  proof_out << "rup >= 0 ;\n";
  ID_Trivial = ++last_proofID;
  protect.insert(ID_Undef);
  protect.insert(ID_Invalid);
  protect.insert(ID_Trivial);
}

std::ostream& operator << (std::ostream& o, const std::vector<Lit>& sol) {
  for (Lit x : sol | std::views::drop(1)) o << proofLit(x);
  return o;
}

ID Logger::solution(const std::vector<Lit>& sol) {
  if (not optimization) return ID_Undef;
  proof_out << "soli" << sol << "\n";
  return ++last_proofID;
}

void Logger::gc() {
  if (unused.empty()) return;
  proof_out << "del id";
  for (ID id : unused) {
    if (not protect.contains(id)) {
      proof_out << " " << id;
    }
  }
  proof_out << "\n";
  unused.clear();
}

void Logger::sat(const std::vector<Lit>& sol) {
  assert(not optimization);
  proof_out << "output NONE\n";
  proof_out << "conclusion SAT :" << sol << "\n";
  proof_out << "end pseudo-Boolean proof\n";
  flush();
}

void Logger::bounds(const bigint& lb) {
  assert(optimization);
  proof_out << "output NONE\n";
  proof_out << "conclusion BOUNDS " << lb << " INF\n";
  proof_out << "end pseudo-Boolean proof\n";
  flush();
}

void Logger::bounds(const bigint& lb, const bigint& ub, const std::vector<Lit>& sol) {
  assert(optimization);
  proof_out << "output NONE\n";
  proof_out << "conclusion BOUNDS " << lb << " " << ub << " :" << sol << "\n";
  proof_out << "end pseudo-Boolean proof\n";
  flush();
}

void Logger::unsat() {
  proof_out << "output NONE\n";
  if (optimization) {
    proof_out << "conclusion BOUNDS INF INF\n";
  } else {
    proof_out << "conclusion UNSAT : " << last_proofID << "\n";
  }
  proof_out << "end pseudo-Boolean proof\n";
  flush();
}

void Logger::optimum(const bigint& opt, const std::vector<Lit>& sol) {
  return bounds(opt, opt, sol);
}

void Logger::bailout() {
  proof_out << "output NONE\n";
  proof_out << "conclusion NONE\n";
  proof_out << "end pseudo-Boolean proof\n";
  flush();
}

autoID::autoID(Logger* logger, ID id) : logger(logger), id(id) {
  if (logger) {
    logger->addRef(id);
  }
}

// We do not care if ID_Undef has a negative refCount
autoID& autoID::operator=(ID newid) {
  if (id == newid) return *this;
  if (logger) {
    logger->addRef(newid);
    logger->delRef(id);
  }
  id = newid;
  return *this;
}

autoID::~autoID() {
  if (logger) {
    logger->delRef(id);
  }
}

autoID::autoID(const autoID& other) : logger(other.logger), id(other.id) {
  if (logger) {
    logger->addRef(id);
  }
}

autoID& autoID::operator = (const autoID& other) {
  if (this == &other) return *this;
  logger = other.logger;
  return *this = other.id;
}

};  // namespace rs

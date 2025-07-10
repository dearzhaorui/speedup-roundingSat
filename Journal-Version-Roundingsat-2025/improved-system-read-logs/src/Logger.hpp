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

#include <ostream>
#include <unordered_set>

#include "Options.hpp"
#include "Stats.hpp"
#include "globals.hpp"
#include "typedefs.hpp"

namespace rs {

class Logger {
public:
  std::ostream& proof_out;
  ID last_formulaID = 0;           // Last loaded axiom
  ID last_proofID = 0;             // Last derived line, starts at #axioms
  ID ID_Trivial = ID_Invalid;      // represents constraint 0 >= 0
  std::vector<ID> unitIDs;
  bool optimization = false;

  // Counts how many objects might use ID in the proof in the future
  // When the count reaches 0 it may be deleted from the proof
  // Needed because Solver and LpSolver delete constraints at different times
  std::unordered_map<ID, size_t> refCount;
  std::vector<ID> unused;
  std::unordered_set<ID> protect;

  Logger(std::ostream& proof_out);
  void init(unsigned int num_constraints);
  void flush() { proof_out.flush(); }

  ID solution(const std::vector<Lit>& sol);
  inline void addRef(ID id) { refCount[id]++; }
  inline void delRef(ID id) {
    if (--refCount[id]==0) {
      refCount.erase(id);
      unused.push_back(id);
    }
  }
  void gc();  // deletes unused constraints with refcount 0

  void sat(const std::vector<Lit>& sol);
  void bounds(const bigint& lb);
  void bounds(const bigint& lb, const bigint& ub, const std::vector<Lit>& sol);
  void unsat();
  void optimum(const bigint& obj, const std::vector<Lit>& sol);
  void bailout();

  inline void logComment([[maybe_unused]] const std::string& comment, [[maybe_unused]] const Stats& sts) {
    if (options.logDebug) {
      proof_out << "* " << sts.getDetTime() << " " << comment << "\n";
    }
  }

  inline void logComment([[maybe_unused]] const std::string& comment) {
    if (options.logDebug) {
      proof_out << "* " << comment << "\n";
    }
  }

};

}  // namespace rs

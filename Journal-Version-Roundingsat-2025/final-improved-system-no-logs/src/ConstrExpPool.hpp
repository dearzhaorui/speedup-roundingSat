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
#include "Env.hpp"
#include "typedefs.hpp"

#include <memory>
#include <vector>

namespace rs {

class Logger;

template <typename CE>
class ConstrExpPool {  // TODO: private constructor for ConstrExp, only accessible to ConstrExpPool?
  size_t n = 0;
  std::vector<CE*> ces;
  std::vector<CE*> availables;
  Logger* plogger;

 public:
  ConstrExpPool(Env& env) : plogger(env.logger.get()) {
    for (CE* ce : ces) ce->initializeLogging(plogger);
  }

  ~ConstrExpPool() {
    for (CE* ce : ces) delete ce;
  }

  void resize(size_t newn) {
    assert(n <= INF);
    n = newn;
    for (CE* ce : ces) ce->resize(n);
  }

  CE* take() {
    assert(ces.size() < 20);  // Sanity check that no large amounts of ConstrExps are created
    if (availables.size() == 0) {
      ces.emplace_back(new CE(*this));
      ces.back()->resize(n);
      ces.back()->initializeLogging(plogger);
      availables.push_back(ces.back());
    }
    CE* result = availables.back();
    availables.pop_back();
    assert(result->isReset());
    assert(result->coefs.size() == n);
    return result;
  }

  void release(CE* ce) {
    assert(std::any_of(ces.begin(), ces.end(), [&](CE* i) { return i == ce; }));
    assert(std::none_of(availables.begin(), availables.end(), [&](CE* i) { return i == ce; }));
    ce->reset();
    availables.push_back(ce);
  }
};

class ConstrExpPools {
  ConstrExpPool<ConstrExp32> ce32s;
  ConstrExpPool<ConstrExp64> ce64s;
  ConstrExpPool<ConstrExp96> ce96s;
  ConstrExpPool<ConstrExp128> ce128s;
  ConstrExpPool<ConstrExpArb> ceArbs;

 public:
  ConstrExpPools(Env& env);
  void resize(size_t newn);

  template <typename SMALL, typename LARGE>
  CePtr<ConstrExp<SMALL, LARGE>> take();  // NOTE: only call specializations

  Ce32 take32();
  Ce64 take64();
  Ce96 take96();
  Ce128 take128();
  CeArb takeArb();
};

}  // namespace rs

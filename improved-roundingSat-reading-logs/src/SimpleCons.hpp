/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

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

#include <iostream>
#include <vector>
#include "typedefs.hpp"

template <typename CF>
struct Term {
  Term(const CF& x, Lit y) : c(x), l(y) {}
  CF c;
  Lit l;
};

template <typename CF>
std::ostream& operator<<(std::ostream& o, const Term<CF>& t) {
  return o << t.c << "x" << t.l;
}

template <typename CF, typename DG>
struct SimpleCons {
  std::vector<Term<CF>> terms;
  DG rhs = 0;
  ID id = ID_Trivial;

  void toNormalFormLit() {
    for (auto& t : terms) {
      if (t.c < 0) {
        rhs -= t.c;
        t.c = -t.c;
        t.l = -t.l;
      }
    }
  }

  void toNormalFormVar() {
    for (auto& t : terms) {
      if (t.l < 0) {
        rhs -= t.c;
        t.c = -t.c;
        t.l = -t.l;
      }
    }
  }
};

template <typename CF, typename DG>
inline std::ostream& operator<<(std::ostream& o, const SimpleCons<CF, DG>& sc) {
  o << sc.id << ": ";
  for (auto& t : sc.terms) o << "+ " << t << " ";
  return o << ">= " << sc.rhs;
}

using SimpleConsInt = SimpleCons<int, long long>;
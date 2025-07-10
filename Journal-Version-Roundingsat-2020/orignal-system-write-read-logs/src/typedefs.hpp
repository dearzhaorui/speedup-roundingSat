/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

Parts of the code were copied or adapted from MiniSat.

MiniSAT -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
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

#include <cassert>
#include <iostream>
#include <limits>
#include <unordered_map>
#include <vector>

using ID = uint64_t;
const ID ID_Undef = std::numeric_limits<ID>::max();
const ID ID_Unsat = ID_Undef - 1;
const ID ID_Trivial = 1;  // represents constraint 0 >= 0

using Var = int;
using Lit = int;
using Coef = int;
using Val = long long;

const Coef INF = 1e9 + 1;       // based on max value of int that still allows addition of two ints
const Val INF_long = 1e15 + 1;  // based on max long range captured by double

using IntVecIt = std::vector<int>::iterator;

using ActValV = long double;
const ActValV actLimitV = (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300 *
                          (ActValV)1e300 * (ActValV)1e300 * (ActValV)1e300;  // ~1e2400 << 2^(2^13)
using ActValC = float;
const ActValC actLimitC = 1e30;  // ~1e30 << 2^(2^7)

// TODO: make below methods part of a Solver object that's passed around
inline bool isTrue(const IntVecIt& level, Lit l) { return level[l] != INF; }
inline bool isFalse(const IntVecIt& level, Lit l) { return level[-l] != INF; }
inline bool isUnit(const IntVecIt& level, Lit l) { return level[l] == 0; }
inline bool isUnknown(const std::vector<int>& pos, Lit l) { return pos[std::abs(l)] == INF; }
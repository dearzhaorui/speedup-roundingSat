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

#include "ConstrExpPool.hpp"

#include "ConstrExp.hpp"

namespace rs {

void ConstrExpPools::resize(size_t newn) {
  ce32s.resize(newn);
  ce64s.resize(newn);
  ce96s.resize(newn);
  ce128s.resize(newn);
  ceArbs.resize(newn);
}

ConstrExpPools::ConstrExpPools(Env& env) : ce32s(env), ce64s(env), ce96s(env), ce128s(env), ceArbs(env) {}

template <>
Ce32 ConstrExpPools::take<int, long long>() {
  return Ce32(ce32s.take());
}
template <>
Ce64 ConstrExpPools::take<long long, int128>() {
  return Ce64(ce64s.take());
}
template <>
Ce96 ConstrExpPools::take<int128, int128>() {
  return Ce96(ce96s.take());
}
template <>
Ce128 ConstrExpPools::take<int128, int256>() {
  return Ce128(ce128s.take());
}
template <>
CeArb ConstrExpPools::take<bigint, bigint>() {
  return CeArb(ceArbs.take());
}

Ce32 ConstrExpPools::take32() { return take<int, long long>(); }
Ce64 ConstrExpPools::take64() { return take<long long, int128>(); }
Ce96 ConstrExpPools::take96() { return take<int128, int128>(); }
Ce128 ConstrExpPools::take128() { return take<int128, int256>(); }
CeArb ConstrExpPools::takeArb() { return take<bigint, bigint>(); }

}  // namespace rs

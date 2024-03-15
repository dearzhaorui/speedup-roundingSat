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

#include <sys/resource.h>
#include <algorithm>
#include <cassert>
#include <iostream>
#include <limits>
#include <numeric>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define _unused(x) ((void)(x))  // marks variables unused in release mode

template <typename T, typename U>
std::ostream& operator<<(std::ostream& os, const std::pair<T, U>& p) {
  os << p.first << "," << p.second;
  return os;
}
template <typename T, typename U>
std::ostream& operator<<(std::ostream& os, const std::unordered_map<T, U>& m) {
  for (const auto& e : m) os << e << ";";
  return os;
}
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& m) {
  for (const auto& e : m) os << e << " ";
  return os;
}

std::ostream& operator<<(std::ostream& os, __int128 x);

namespace aux {

#ifndef __GLIBCXX_TYPE_INT_N_0
namespace std {
template <>
class numeric_limits<__int128> {
 public:
  static __int128 max() {
    __int128 x;
    x = 170141183460469;
    x *= 1000000000000000;
    x += 231731687303715;
    x *= 1000000000;
    x += 884105727;
    return x;  // which is 2^127-1
  };
  static __int128 min() { return -max() + 1; };
  const static bool is_specialized = true;
};
}  // namespace std
#endif

template <typename T>
T str2num(const std::string&& description) {
  T result = 0;
  for (unsigned int i = 0; i < description.size(); ++i) {
    result *= 10;
    result += (int)(description[i] - '0');
  }
  return result;
}

template <typename T>
std::string num2str(T x) {
  if (x < 0) return "-" + num2str(-x);
  if (x == 0) return "0";
  std::string result = "";
  result.reserve(10);
  while (x > 0) {
    result.push_back(((int)(x % 10)) + '0');
    x /= 10;
  }
  reverse(result.begin(), result.end());
  return result;
}

template <typename T>
inline void swapErase(T& indexable, size_t index) {
  indexable[index] = indexable.back();
  indexable.pop_back();
}

template <typename T, typename U>
inline bool contains(const T& v, const U& x) {
  return std::find(v.cbegin(), v.cend(), x) != v.cend();
}

template <typename T>
inline T ceildiv(const T& p, const T& q) {
  assert(q > 0);
  assert(p >= 0);
  return (p + q - 1) / q;
}  // NOTE: potential overflow
template <typename T>
inline T floordiv(const T& p, const T& q) {
  assert(q > 0);
  assert(p >= 0);
  return p / q;
}
template <typename T>
inline T ceildiv_safe(const T& p, const T& q) {
  assert(q > 0);
  return (p < 0 ? -floordiv(-p, q) : ceildiv(p, q));
}
template <typename T>
inline T floordiv_safe(const T& p, const T& q) {
  assert(q > 0);
  return (p < 0 ? -ceildiv(-p, q) : floordiv(p, q));
}
template <typename T>
inline T mod_safe(const T& p, const T& q) {
  assert(q > 0);
  return p < 0 ? q - (-p % q) : p % q;
}

unsigned int gcd(unsigned int u, unsigned int v);  // TODO: C++17 provides std::gcd

// Minisat cpuTime function
static inline double cpuTime() {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

template <typename T>
void resizeIntMap(std::vector<T>& _map, typename std::vector<T>::iterator& map, int size, int resize_factor, T init) {
  assert(size < (1 << 28));
  int oldsize = (_map.size() - 1) / 2;
  if (oldsize >= size) return;
  int newsize = oldsize;
  while (newsize < size) newsize = newsize * resize_factor + 1;
  _map.resize(2 * newsize + 1);
  map = _map.begin() + newsize;
  int i = _map.size() - 1;
  for (; i > newsize + oldsize; --i) _map[i] = init;
  for (; i >= newsize - oldsize; --i) _map[i] = _map[i - newsize + oldsize];
  for (; i >= 0; --i) _map[i] = init;
}

template <typename T>
T median(std::vector<T>& v) {
  assert(v.size() > 0);
  size_t n = v.size() / 2;
  std::nth_element(v.begin(), v.begin() + n, v.end());
  return v[n];
}

template <typename T>
double average(const std::vector<T>& v) {
  assert(v.size() > 0);
  return std::accumulate(v.begin(), v.end(), 0.0) / (double)v.size();
}

template <typename T>
T min(const std::vector<T>& v) {
  return *std::min_element(v.begin(), v.end());
}

template <typename T>
T max(const std::vector<T>& v) {
  return *std::max_element(v.begin(), v.end());
}

}  // namespace aux
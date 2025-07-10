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

#include <limits>
#include <numeric>

namespace rs::aux {

template <typename T>
T ceildiv(const T& p, const T& q) {
	 // Computes ceil(p/q) for p, q > 0.
	 // NOTE: potential overflow (when calculating p + q).
  assert(q > 0);
  assert(p >= 0);
  return (p + q - 1) / q;
}
template <typename T>
T floordiv(const T& p, const T& q) {
    // Computes floor(p/q) for p, q > 0.
  assert(q > 0);
  assert(p >= 0);
  return p / q;
}
template <typename T>
T ceildiv_safe(const T& p, const T& q) {
	// Computes ceil(p/q) for q > 0.
	// Since C++ rounds towards 0, we require a case distinction on the sign of p.
  assert(q > 0);
  return (p < 0) ? (-floordiv<T>(-p, q)) : ceildiv(p, q);
}
template <typename T>
T floordiv_safe(const T& p, const T& q) {
	// Computes floor(p/q) for q > 0.
	// Since C++ rounds towards 0, we require a case distinction on the sign of p.
  assert(q > 0);
  return (p < 0) ? (-ceildiv<T>(-p, q)) : floordiv(p, q);
}
template <typename T>
T mod_safe(const T& p, const T& q) {
	// Computes p mod q for q > 0.
	// Since C++ rounds towards 0, we require a case distinction: if p<0, then the remainder may be negative.
  assert(q > 0);
  T r = p % q;
  return (r >= 0) ? r : (q + r);
}

template <typename T>
T median(std::vector<T>& v) {
	// Compute the median of a vector of odd length.
  assert(v.size() > 0);
  assert(v.size() % 2 == 1);
  size_t n = v.size() / 2;
  std::nth_element(v.begin(), v.begin() + n, v.end());
  return v[n];
}

template <typename T>
double average(const std::vector<T>& v) {
  assert(v.size() > 0);
  return std::accumulate(v.begin(), v.end(), 0.0) / (double)v.size();
}

// Extensions of common math functions to wider types, for template uniformity

template <typename T>
T abs(const T& x) {
  return std::abs(x);
}
template <>
inline bigint abs(const bigint& x) {
  return boost::multiprecision::abs(x);
}
template <>
inline boost::multiprecision::int128_t abs(const boost::multiprecision::int128_t& x) {
  return boost::multiprecision::abs(x);
}
template <>
inline int256 abs(const int256& x) {
  return boost::multiprecision::abs(x);
}

template <typename T>
T gcd(const T& x, const T& y) {
  return std::gcd(x, y);
}
template <>
inline bigint gcd(const bigint& x, const bigint& y) {
  return boost::multiprecision::gcd(x, y);
}
template <>
inline boost::multiprecision::int128_t gcd(const boost::multiprecision::int128_t& x,
                                           const boost::multiprecision::int128_t& y) {
  return boost::multiprecision::gcd(x, y);
}
template <>
inline int256 gcd(const int256& x, const int256& y) {
  return boost::multiprecision::gcd(x, y);
}

template <typename T>
T lcm(const T& x, const T& y) {
  return std::lcm(x, y);
}
template <>
inline bigint lcm(const bigint& x, const bigint& y) {
  return boost::multiprecision::lcm(x, y);
}
template <>
inline boost::multiprecision::int128_t lcm(const boost::multiprecision::int128_t& x,
                                           const boost::multiprecision::int128_t& y) {
  return boost::multiprecision::lcm(x, y);
}
template <>
inline int256 lcm(const int256& x, const int256& y) {
  return boost::multiprecision::lcm(x, y);
}

template <typename T>
unsigned msb(const T& x) {
  assert(x > 0);
  // return std::bit_floor(x); // C++20
  return boost::multiprecision::msb(boost::multiprecision::uint128_t(x));
}
template <>
inline unsigned msb(const bigint& x) {
  assert(x > 0);
  return boost::multiprecision::msb(x);
}
template <>
inline unsigned msb(const boost::multiprecision::int128_t& x) {
  assert(x > 0);
  return boost::multiprecision::msb(x);
}
template <>
inline unsigned msb(const int256& x) {
  assert(x > 0);
  return boost::multiprecision::msb(x);
}

template <typename T>
T pow(const T& x, unsigned y) {
  return std::pow(x, y);
}
template <>
inline bigint pow(const bigint& x, unsigned y) {
  return boost::multiprecision::pow(x, y);
}
template <>
inline boost::multiprecision::int128_t pow(const boost::multiprecision::int128_t& x, unsigned y) {
  return boost::multiprecision::pow(x, y);
}
template <>
inline int256 pow(const int256& x, unsigned y) {
  return boost::multiprecision::pow(x, y);
}

template <typename T>
bool fits([[maybe_unused]] const bigint& x) {
  return false;
}
template <>
inline bool fits<int>(const bigint& x) {
  return aux::abs(x) <= bigint(limit32);
}
template <>
inline bool fits<long long>(const bigint& x) {
  return aux::abs(x) <= bigint(limit64);
}
template <>
inline bool fits<int128>(const bigint& x) {
  return aux::abs(x) <= bigint(limit128);
}
template <>
inline bool fits<int256>(const bigint& x) {
  return aux::abs(x) <= bigint(limit256);
}
template <>
inline bool fits<bigint>([[maybe_unused]] const bigint& x) {
  return true;
}
template <typename T, typename S>
bool fitsIn([[maybe_unused]] const S& x) {
  return fits<T>(bigint(x));
}

#ifdef __APPLE__
template <>
inline int128 abs(const int128& x) {
  return x < 0 ? -x : x;
}
template <>
inline int128 gcd(const int128& x, const int128& y) {
  return static_cast<int128>(
      boost::multiprecision::gcd(boost::multiprecision::int128_t(x), boost::multiprecision::int128_t(y)));
}
template <>
inline unsigned msb(const int128& x) {
  return boost::multiprecision::msb(boost::multiprecision::uint128_t(x));
}
template <>
inline int128 pow(const int128& x, unsigned y) {
  return static_cast<int128>(boost::multiprecision::pow(boost::multiprecision::int128_t(x), y));
}
#endif

}  // namespace rs::aux

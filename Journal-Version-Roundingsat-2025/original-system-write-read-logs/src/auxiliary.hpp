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

// NOTE: This file may not be called auxiliary.hpp, because this is a forbidden file name on windows.

#pragma once

#define _unused(x) ((void)(x))  // marks variables unused in release mode, use [[maybe_unused]] where possible

#include <algorithm>
#include <cassert>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

namespace rs {

template <typename T, typename U>
std::ostream& operator<<(std::ostream& os, const std::pair<T, U>& p) {
    // Outputs both elements of the pair, separated by a comma.
  os << p.first << "," << p.second;
  return os;
}
template <typename T, typename U>
std::ostream& operator<<(std::ostream& os, const std::unordered_map<T, U>& m) {
    // Outputs map in the format key1,value1;key2,value2;...
  for (const auto& e : m) os << e << ";";
  return os;
}
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& m) {
    // Outputs vector in the format value1 value2 ...
  for (const auto& e : m) os << e << " ";
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const __int128& x) {
    // Outputs an int128 as a string.
  if (x < 0) return os << "-" << -x;
  if (x < 10) return os << (char)(x + '0');
  return os << x / 10 << (char)(x % 10 + '0');
}

namespace aux {

template <typename T>
T sto(const std::string& s) {
  return std::stold(s);
}
template <>
inline double sto(const std::string& s) {
  return std::stod(s);
}
template <>
inline std::string sto(const std::string& s) {
  return s;
}

template <typename T>
std::string tos(const T& t) {
  return std::to_string(t);
}
template <>
inline std::string tos(const std::string& s) {
  return s;
}

template <typename T>
void swapErase(T& indexable, size_t index) {
  indexable[index] = std::move(indexable.back());
  indexable.pop_back();
}

// ranges::contains // C++23
template <typename T, typename U>
bool contains(const T& v, const U& x) {
  return std::find(v.cbegin(), v.cend(), x) != v.cend();
}

template <typename T>
void resizeIntMap(std::vector<T>& _map, typename std::vector<T>::iterator& map, int size, int resize_factor, T init) {
    // Resizes the vector _map to a length which is at least size (and at most size * resize_factor).
    // It then moves the original _map to the center of the resized vector, and then pads both ends using the element init.
    // After the change, the iterator map will point to the center of the array.
    // This function implicitly assumes that the original vector length is odd, otherwise one element of the original _map is lost.
  assert(size < (1 << 28));
  assert(_map.size() % 2 == 1);
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

}  // namespace aux

}  // namespace rs

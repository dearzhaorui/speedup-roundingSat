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

#include "aux.hpp"

struct IntSet {  // TODO: template to long long, int128, ...?
 private:
  std::vector<bool> _values = {false};
  std::vector<bool>::iterator values = _values.begin();
  static constexpr bool _unused_() { return false; }
  const int resize_factor = 2;

 public:
  std::vector<int> keys;

  IntSet() {}
  IntSet(int size, const std::vector<int>& ints) {
    resize(size);
    for (int i : ints) add(i);
  }

  void reset() {
    for (int k : keys) values[k] = _unused_();
    keys.clear();
  }

  inline void resize(int size) { aux::resizeIntMap(_values, values, size, resize_factor, _unused_()); }
  inline size_t size() const { return keys.size(); }

  inline bool has(int key) const {
    return _values.size() > (unsigned int)2 * std::abs(key) && values[key] != _unused_();
  }
  void add(int key) {
    if (_values.size() <= (unsigned int)2 * std::abs(key)) resize(std::abs(key));
    if (values[key] != _unused_()) return;
    assert(!aux::contains(keys, key));
    values[key] = !_unused_();
    keys.push_back(key);
  }

  std::ostream& operator<<(std::ostream& o) const {
    for (int k : keys)
      if (has(k)) o << k << " ";
    return o;
  }
};

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
#include "typedefs.hpp"

namespace rs {

struct CRef {
  uint32_t ofs;
  bool operator==(CRef const& o) const { return ofs == o.ofs; }
  bool operator!=(CRef const& o) const { return ofs != o.ofs; }
  bool operator<(CRef const& o) const { return ofs < o.ofs; }
  std::ostream& operator<<(std::ostream& os) { return os << ofs; }
};
const CRef CRef_Undef = {std::numeric_limits<uint32_t>::max()};

// TODO: make below methods part of a Solver object that's passed around
inline bool isTrue(const IntVecIt& level, Lit l) { return level[l] != INF; }
inline bool isFalse(const IntVecIt& level, Lit l) { return level[-l] != INF; }
inline bool isUnit(const IntVecIt& level, Lit l) { return level[l] == 0; }

/**
 * @brief Check if literal is assigned.
 *
 * @param pos Vector of variable assignments.
 * @param l Literal to check.
 * @return true If unassigned.
 * @return false If assigned.
 */
inline bool isUnknown(const std::vector<int>& pos, Lit l) { return pos[toVar(l)] == INF; }

/**
 * @brief Check if the reason for assignment of the literal was a decision.
 *
 * @param reasons Vector of reasons for the literals.
 * @param l Literal to check.
 * @return true If literal was decided on the current trail.
 * @return false If literal was not decided on the current trail.
 */
inline bool isDecided(const std::vector<CRef>& reasons, Lit l) { return reasons[toVar(l)] == CRef_Undef; }

/**
 * @brief Check if the assignment of the literal was a propagated.
 *
 * @param reasons Vector of reasons for the literals.
 * @param l Literal to check.
 * @return true If literal was propagated on the current trail.
 * @return false If literal was not propagated on the current trail.
 */
inline bool isPropagated(const std::vector<CRef>& reasons, Lit l) { return !isDecided(reasons, l); }

struct Watch {
  int32_t iID; // internal ID, the idx of slack in slackMCoefV
  int idx;  // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
  struct Header {
    unsigned cSize      : 2;  // the value means coefOrLit is: 0 (coef), 1 (SIGN_PTR_64), 2 (SIGN_PTR_128), 3 (SIGN_PTR_BIGINT)
    long long coefOrLit : 62; // the value is eigher coef, or pointer to different sizes
  } header;

  Watch() {iID = 0; idx = 0; header = {0, 0}; };
  // clause or cardinality
  Watch(int32_t iid, int i) :                           iID(iid), idx(i) {header = {0, 0};};
  // watched or counting PB
  Watch(int32_t iid, int i, long long val) :            iID(iid), idx(i) {header = {0, val};};
  Watch(int32_t iid, int i, unsigned int csize, long long val) : iID(iid), idx(i) {header = {csize, val};};

  // copy constructor
  Watch(const Watch& other): iID(other.iID), idx(other.idx), header(other.header) {}
  // move constructor
  Watch(Watch&& other) noexcept : iID(other.iID), idx(other.idx), header(other.header) {}

  inline bool isClause ()       const {return idx < -1;}
  inline bool isCard ()         const {return idx >= 0 && idx < INF;}
  inline bool isSimple ()       const {return idx < INF;}
  inline bool isPB ()           const {return idx >= INF;}
  inline bool isCounting()      const {return header.coefOrLit > 0; assert(idx >= INF);}
  inline bool isWatched()       const {return header.coefOrLit < 0; assert(idx >= INF);}
  inline int  cachedLit()       const {assert(isClause()); return idx + INF; }
  inline bool isCoef()          const {return (header.cSize == 0); }
  inline long long coeffOfLit() const {assert(isCoef()); return header.coefOrLit; }

  // SIGN_PTR_64 or SIGN_PTR_128 or SIGN_PTR_BIGINT
  inline unsigned int coefSize() const  { assert(!isCoef()); return header.cSize; }
  inline long long ptrVal()      const  { return std::abs(header.coefOrLit);}
  inline void setPtr(long long x) { assert(!isCoef()); header.coefOrLit = x; }

  // copy assignment operator
  Watch& operator=(const Watch& other) {
    if (this != &other) {
      iID    = other.iID;
      idx    = other.idx;
      header = other.header;
    }
    return *this;
  }

  // move assignment operator
  Watch& operator=(Watch&& other) noexcept {
    if (this != &other) {
      iID    = other.iID;
      idx    = other.idx;
      header = other.header;
    }
    return *this;
  }

  // for debugging
  inline BigVal coef() const {
    if (!isPB()) return BigVal(1);
    if (isCoef()) return BigVal(std::abs(coeffOfLit()));
    else if (coefSize() == SIGN_PTR_64) return BigVal(*((int64_t*)ptrVal()));
    else if (coefSize() == SIGN_PTR_128) return BigVal(*((int128*)ptrVal()));
    else return BigVal(*((bigint*)ptrVal()));
  }
};

inline std::ostream& operator<<(std::ostream& os, const Watch& w) { // if coef is -1:clause/card, 0:ptr, otherwise: PB ctr
  os << "Watch: (iID " << w.iID << ", idx " << w.idx-INF << ", LS " << w.idx << ", INF " << INF << ", ";
  if (w.isClause()) os << "cachedLit "   << w.cachedLit()   << ") ";
  else if (w.isCard())   os << "card coef "   << 1               << ") ";
  else {
    if (w.isCoef()) os << "coef " << std::abs(w.coeffOfLit()) << ") ";
    else {
      long long ptr       = w.ptrVal();
      unsigned int csize  = w.coefSize();
      os << "csize " << csize << ", ptr " << ptr << ", coef ";
      if      (csize == SIGN_PTR_64)  os << *((int64_t*)ptr) << ") ";
      else if (csize == SIGN_PTR_128) os << BigVal(*((int128*)ptr))  << ") ";
      else                            os << *((bigint*)ptr)   << ") ";
    }
  }
  return os;
}

struct SlackMC {
  unsigned  removed:  1;   // default 0
  unsigned  isVal:    1;   // default 1
  long long slackMC:  62;  // the value is slack-maxCoef or pointer ('abs' is address, positive: int128, negative: bigint)

  SlackMC() {removed = 0; isVal = 1; slackMC = 0;}; // this is a slack value by default, not a pointer
  SlackMC(uint r, uint iv, long long smc): removed(r), isVal(iv), slackMC(smc) {};
  SlackMC(uint r, int128* p) : removed(r), isVal(0), slackMC(reinterpret_cast<long long>(p)) {
    assert(reinterpret_cast<long long>(p) <= limit64);
    assert(*((int128*)std::abs(slackMC)) == static_cast<int128>(*p));
  };
  SlackMC(uint r, bigint* p) : removed(r), isVal(0), slackMC(-reinterpret_cast<long long>(p)) {
    assert(reinterpret_cast<long long>(p) <= limit64);
    assert(*((bigint*)std::abs(slackMC)) == static_cast<bigint>(*p));
  };
  inline long long ptrVal() const {assert(isVal == 0); return std::abs(slackMC);}
  template<typename T> inline T& dereference() const;
  inline void setIsCoef() {isVal = 1;}

  inline unsigned int valueSize() const  {
    assert(!isVal); 
    return (slackMC >= 0? SIGN_PTR_128 : SIGN_PTR_BIGINT);
  }

  // Copy Constructor
  SlackMC(const SlackMC& other) : removed(other.removed), isVal(other.isVal), slackMC(other.slackMC) {}
  // Move Constructor
  SlackMC(SlackMC&& other) noexcept : removed(other.removed), isVal(other.isVal), slackMC(other.slackMC) {other.setIsCoef();}

  // copy assignment operator
  SlackMC& operator=(const SlackMC& other) {
    if (this != &other) {
      clear();
      assert(isVal);
      removed = other.removed;
      isVal   = other.isVal;
      slackMC = other.slackMC;
    }
    return *this;
  }

  // move assignment operator
  SlackMC& operator=(SlackMC&& other) noexcept {
    if (this != &other) {
      clear();
      assert(isVal);
      removed = other.removed;
      isVal   = other.isVal;
      slackMC = other.slackMC;
      other.setIsCoef();
    }
    return *this;
  }

  inline void clear() { // should be explicitly called when the ctr is to be removed
    if (!isVal) {
      if (valueSize() == SIGN_PTR_128) { delete (reinterpret_cast<int128*>(ptrVal())); }
      else                             { delete (reinterpret_cast<bigint*>(ptrVal())); }
      setIsCoef();
    }
  }

  // for debugging
  inline BigVal slkMC () const {
    if (isVal) return BigVal(slackMC);
    else if (valueSize() == SIGN_PTR_128) return BigVal(*(reinterpret_cast<int128*>(ptrVal())));
    else return *(reinterpret_cast<bigint*>(ptrVal()));
  }

  ~SlackMC() {
    clear();
  }
};

template<> inline int128& SlackMC::dereference<int128>() const {
  assert(slackMC>0);
  return *reinterpret_cast<int128*>(slackMC);
}
template<> inline bigint& SlackMC::dereference<bigint>() const {
  assert(slackMC<0);
  return *reinterpret_cast<bigint*>(-slackMC);
}


inline std::ostream& operator << (std::ostream& os, const SlackMC& s) {
  os << "SlackMC: (isValue? " << s.isVal << " ";
  if (s.isVal)                            os << "val = " << s.slackMC << " ";
  else if (s.valueSize() == SIGN_PTR_128) os << "int128(val) = " << BigVal(*(reinterpret_cast<int128*>(s.ptrVal()))) << " ";
  else                                    os << "bigint(val) = " << *(reinterpret_cast<bigint*>(s.ptrVal())) << " ";
  return os;
}

// ---------------------------------------------------------------------
// Memory. Maximum supported size of learnt constraint database is 16GB

struct ConstraintAllocator {
  uint32_t* memory = nullptr;  // TODO: why not uint64_t?
  uint32_t at = 0, cap = 0;
  uint32_t wasted = 0;  // for GC
  ~ConstraintAllocator() { free(memory); }
  void capacity(uint32_t min_cap);
  template <typename C>
  C* alloc(int nTerms) {
    uint32_t oldAt = at;
    at += C::getMemSize(nTerms);
    capacity(at);
    return (C*)(memory + oldAt);
  }
  Constr& operator[](CRef cr) { return (Constr&)*(memory + cr.ofs); }
  const Constr& operator[](CRef cr) const { return (Constr&)*(memory + cr.ofs); }
};

class OutOfMemoryException {};
static inline void* xrealloc(void* ptr, size_t size) {
  void* mem = realloc(ptr, size);
  if (mem == NULL && errno == ENOMEM)
    throw OutOfMemoryException();
  else
    return mem;
}

// ---------------------------------------------------------------------
// Order heap

struct OrderHeap {  // segment tree (fast implementation of priority queue).
  std::vector<ActValV>& activity;
  int cap = 0;
  std::vector<Var> tree = {-1, -1};

  OrderHeap(std::vector<ActValV>& a) : activity(a) {}

  void resize(int newsize);
  void recalculate();
  void percolateUp(Var x);
  bool empty() const;
  void clear(); // only for reading execution info
  bool inHeap(Var x) const;
  void insert(Var x);
  Var removeMax();
};

}  // namespace rs

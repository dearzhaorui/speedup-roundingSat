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

#include <ostream>
#include "Constraint.hpp"
#include "typedefs.hpp"

struct CRef {
  uint32_t ofs;
  bool operator==(CRef const& o) const { return ofs == o.ofs; }
  bool operator!=(CRef const& o) const { return ofs != o.ofs; }
  bool operator<(CRef const& o) const { return ofs < o.ofs; }  
  std::ostream& operator<<(std::ostream& os) { return os << ofs; }
};
const CRef CRef_Undef = {std::numeric_limits<uint32_t>::max()};
const CRef CRef_Unsat = {std::numeric_limits<uint32_t>::max() - 1};  // TODO: needed?

struct Watch {
  uint32_t iID; // internal ID, the position of slack in slackMM
  int idx;  // >=0: index of watched literal (counting/watched propagation). <0: blocked literal (clausal propagation).
  int coefOrLit;
  Watch() {iID = 1; idx = 0; coefOrLit = 0; };
  Watch(uint32_t iid, int i, int c) : iID(iid), idx(i), coefOrLit(c) {};
  bool operator==(const Watch& other) const { return other.idx == idx && other.coefOrLit == coefOrLit && other.iID == iID; }
  
  inline bool isBin()          const {return idx == -1;}
  inline bool isClause ()      const {return idx <  -1;}
  inline bool isCard ()        const {return idx >= 0 && idx % 2 == 1;}
  inline bool isPB ()          const {return idx >= 0 && idx % 2 == 0;}
  
  int otherBinLit()   const  {assert(isBin());  return coefOrLit;}
  int coeffOfLit()    const  {assert(isPB());   return coefOrLit;}
};

/*
 * FORMULA constraints are original input formula constraints that are only deleted when satisfied at root.
 * AUXILIARY constraints are non-formula constraints that are only deleted when satisfied at root.
 * EXTERNAL constraints are non-formula constraints that are never deleted.
 * LEARNT constraints are implied by any combination of the above, and may be deleted heuristically.
 */

enum ConstraintType { FORMULA, AUXILIARY, EXTERNAL, LEARNT };
enum PropType { CLAUSE, CARDINALITY, COUNTINGPB, WATCHEDPB };
class Solver;
struct Constr {  // internal solver constraint optimized for fast propagation
  static int sz_constr(int length) { return (sizeof(Constr) + sizeof(int) * length) / sizeof(uint32_t); }
  ID id;
  Val degree;
  // NOTE: above attributes not strictly needed in cache-sensitive Constr, but it did not matter after testing
  struct {
    unsigned unused : 1;
    unsigned type : 2;
    unsigned lbd : 29;
    unsigned propType: 2;  // 0 clause, 1 cardinality, 2 countingPB, 3 watchedPB
    unsigned size : 30;
  } header;
  long long ntrailpops;
  ActValC act;
  unsigned int watchIdx;
  int data[];

  inline bool isClause() const { return (PropType)header.propType == PropType::CLAUSE; }
  inline bool isCard()   const { return (PropType)header.propType == PropType::CARDINALITY; }
  inline bool isSimple() const { return header.propType < 2; }
  inline int getMemSize() const { return sz_constr(size() + (isSimple() ? 0 : size())); }
  inline unsigned int size() const { return header.size; }
  inline void setType(ConstraintType t) { header.type = (unsigned int)t; }
  inline ConstraintType getType() const { return (ConstraintType)header.type; }
  inline void setLBD(unsigned int lbd) { header.lbd = std::min(header.lbd, lbd); }
  inline unsigned int lbd() const { return header.lbd; }
  inline bool isCounting()  const { return (PropType)header.propType == PropType::COUNTINGPB; }
  inline bool isWatchedPB() const { return (PropType)header.propType == PropType::WATCHEDPB; }
  inline void setCounting(bool c) { if(c)  header.propType = (unsigned int)PropType::COUNTINGPB; }
  inline Coef largestCoef() const {
    assert(!isSimple());
    assert(!options.oldProp);
    return std::abs(data[0]);
  }
  inline Coef coef(unsigned int i) const {
    return isSimple() ? 1 : (options.oldProp ? data[i + size()] : std::abs(data[i << 1]));
  }
  inline Lit lit(unsigned int i) const { return (isSimple() || options.oldProp) ? data[i] : data[(i << 1) + 1]; }
  inline bool isWatched(unsigned int i) const {
    assert(!isSimple());
    assert(!isCounting());
    assert(!options.oldProp);
    return data[i] < 0;
  }
  double strength() const;
  template <typename S, typename L>
  inline void toConstraint(Constraint<S, L>& out) const {
    assert(out.isReset());  // don't use a Constraint used by other stuff
    out.addRhs(degree);
    for (size_t i = 0; i < size(); ++i) {
      assert(coef(i) != 0);
      out.addLhs(coef(i), lit(i));
    }
    out.degree = degree;
    out.id = id;
    if (options.oldProp && !isSimple()) out.sortInDecreasingCoefOrder();
    if (out.plogger) out.resetBuffer(id);
  }
  template <typename CF, typename DG>
  SimpleCons<CF, DG> toSimpleCons() const {
    SimpleCons<CF, DG> result;
    result.rhs = degree;
    result.id = id;
    result.terms.reserve(size());
    for (unsigned int i = 0; i < size(); ++i) result.terms.emplace_back(coef(i), lit(i));
    return result;
  }
  std::ostream& operator<<(std::ostream& o) {
    for (size_t i = 0; i < size(); ++i) {
      o << coef(i) << "x" << lit(i) << " ";
    }
    o << ">= " << degree << "\n";
    return o;
  }
};

// ---------------------------------------------------------------------
// Memory. Maximum supported size of learnt constraint database is 16GB

struct ConstraintAllocator {
  uint32_t* memory;  // TODO: why not uint64_t?
  uint32_t at = 0, cap = 0;
  uint32_t wasted = 0;  // for GC
  void capacity(uint32_t min_cap);
  CRef alloc(intConstr& constraint, ConstraintType type, ID id, Val degree);
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

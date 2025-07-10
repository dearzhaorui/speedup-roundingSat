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

#include "SolverStructs.hpp"
#include "Options.hpp"
#include "globals.hpp"

double Constr::strength() const {
  if (isSimple()) return size() / (double)degree;
  double coefsum = 0;
  for (unsigned int i = 0; i < size(); ++i) coefsum += coef(i);
  return coefsum / (double)degree;
}

void ConstraintAllocator::capacity(uint32_t min_cap) {
  if (cap >= min_cap) return;

  uint32_t prev_cap = cap;
  while (cap < min_cap) {
    // NOTE: Multiply by a factor (13/8) without causing overflow, then add 2 and make the
    // result even by clearing the least significant bit. The resulting sequence of capacities
    // is carefully chosen to hit a maximum capacity that is close to the '2^32-1' limit when
    // using 'uint32_t' as indices so that as much as possible of this space can be used.
    uint32_t delta = ((cap >> 1) + (cap >> 3) + 2) & ~1;
    cap += delta;
    if (cap <= prev_cap) throw OutOfMemoryException();
  }

  assert(cap > 0);
  memory = (uint32_t*)xrealloc(memory, sizeof(uint32_t) * cap);
}

// TODO: allow constraints with 10^18 bit degree
CRef ConstraintAllocator::alloc(intConstr& constraint, ConstraintType type, ID id, Val degree) {
  assert(constraint.getDegree() > 0);
  assert(constraint.getDegree() < INF);
  assert(constraint.isSaturated());
  // as the constraint is saturated, the coefficients are between 1 and 1e9 as well.
  assert(!constraint.vars.empty());
  assert(id > 0);
  unsigned int length = constraint.vars.size();
  bool asClause = options.clauseProp && degree == 1;
  bool asCard = !asClause && options.cardProp && std::abs(constraint.coefs[constraint.vars[0]]) == 1;

  // note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
  // during maintenance of watches the order will be shuffled.
  uint32_t old_at = at;
  at += Constr::sz_constr(length + ((asClause || asCard) ? 0 : length));
  capacity(at);
  Constr* constr = (Constr*)(memory + old_at);
  new (constr) Constr;
  constr->id = id;
  constr->act = 0;
  constr->degree = degree;
  constr->header = {0, (unsigned int)type, 0x1FFFFFFF, (asClause? (unsigned int)PropType::CLAUSE : (asCard? (unsigned int)PropType::CARDINALITY : 3)), length}; // default is WATCHEDPB
  constr->ntrailpops = -1;
  constr->watchIdx = 0;
  assert(asClause == constr->isClause());
  assert(asCard == constr->isCard());
  for (unsigned int i = 0; i < length; ++i) {
    Var v = constraint.vars[i];
    assert(constraint.getLit(v) != 0);
    if (constr->isSimple())
      constr->data[i] = constraint.getLit(v);
    else {
      constr->data[(i << 1)] = std::abs(constraint.coefs[v]);
      constr->data[(i << 1) + 1] = constraint.getLit(v);
    }
  }
  return CRef{old_at};
}

// segment tree (fast implementation of priority queue).
void OrderHeap::resize(int newsize) {
  if (cap >= newsize) return;
  // insert elements in such order that tie breaking remains intact
  std::vector<Var> variables;
  while (!empty()) variables.push_back(removeMax());
  tree.clear();
  while (cap < newsize) cap = cap * options.resize_factor + 1;
  tree.resize(2 * (cap + 1), -1);
  for (Var x : variables) insert(x);
}
void OrderHeap::recalculate() {  // TODO: more efficient implementation
  // insert elements in such order that tie breaking remains intact
  std::vector<Var> variables;
  while (!empty()) variables.push_back(removeMax());
  tree.clear();
  tree.resize(2 * (cap + 1), -1);
  for (Var x : variables) insert(x);
}
void OrderHeap::percolateUp(Var x) {
  for (int at = x + cap + 1; at > 1; at >>= 1) {
    if (tree[at ^ 1] == -1 || activity[x] > activity[tree[at ^ 1]])
      tree[at >> 1] = x;
    else
      break;
  }
}
bool OrderHeap::empty() const { return tree[1] == -1; }
bool OrderHeap::inHeap(Var x) const { return tree[x + cap + 1] != -1; }
void OrderHeap::insert(Var x) {
  assert(x <= cap);
  if (inHeap(x)) return;
  tree[x + cap + 1] = x;
  percolateUp(x);
}
Var OrderHeap::removeMax() {
  Var x = tree[1];
  assert(x != -1);
  tree[x + cap + 1] = -1;
  for (int at = x + cap + 1; at > 1; at >>= 1) {
    if (tree[at ^ 1] != -1 && (tree[at] == -1 || activity[tree[at ^ 1]] > activity[tree[at]]))
      tree[at >> 1] = tree[at ^ 1];
    else
      tree[at >> 1] = tree[at];
  }
  return x;
}

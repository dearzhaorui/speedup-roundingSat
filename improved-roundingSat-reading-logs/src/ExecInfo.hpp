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

struct CleanupInfo {
  uint id;
  uint nDecs;
  uint nConfs;
  std::vector<uint> IDs;
  CleanupInfo() {id = 0; nDecs = 0; nConfs = 0;}
  CleanupInfo(int i, uint d, uint c): id(i), nDecs(d), nConfs(c) {}
  bool isEmpty() {return (id == 0);}
};
struct RestartInfo {
  uint id;
  uint nDecs;
  uint nConfs;
  RestartInfo() {id = 0; nDecs = 0; nConfs = 0;}
  RestartInfo(int i, uint d, uint c): id(i), nDecs(d), nConfs(c) {}
  bool isEmpty() {return (id == 0);}
};

struct DecisionInfo{
  int decisionLit;
  uint nConfs;
  int trailSize;
  DecisionInfo(int dec, uint nc, int size): decisionLit(dec),nConfs(nc),trailSize(size) {}
};

struct Result{
  uint nConflicts;
  uint nDecisions;
  int nSolutionsFound;
  int nRestarts;
  uint nCleanups;
  int bestCost;
  int status;
  uint nPBLemmas;
  uint nClauseLemmas;
  uint nCut;
};

struct OBJ{
  //std::vector<std::pair<int,int>> lhs;
  int id;
  int dl;
  //int rhs;
  OBJ(int id, int d):id(id), dl(d) {}
};

struct PBLemma{
  std::vector<std::pair<int,int>> lhs;
  int rhs;
  uint id;
  int nCut;
  int DL;
  int btLevel;
  int size;
  bool isInit;
  int activity;
  int LBD;
  bool retur;
  int trailSize;
  PBLemma(int rhs, int id, int nCut, int dl, int bt, int s, bool i, int a, int lbd, bool ret, int ts):rhs(rhs),id(id),nCut(nCut),DL(dl),btLevel(bt),size(s),isInit(i),activity(a),LBD(lbd),retur(ret),trailSize(ts) {}
};

struct ClauseLemma{
  std::vector<int> lemma;
  uint id;
  int nCut;
  int DL;
  int btLevel;
  int size;
  bool isInit;
  int activity;
  int LBD;
  int trailSize;
  ClauseLemma(std::vector<int>& lemma, int id, int nCut, int dl, int bt, int s, bool i, int a, int lbd, int ts):lemma(lemma),id(id),nCut(nCut),DL(dl),btLevel(bt),size(s),isInit(i),activity(a),LBD(lbd),trailSize(ts) {}
};

#include "file.hpp"

namespace rs {
  
File::File (Solver *s, std::string nameFile): solver(s) {
  open(nameFile);
}

#define getNext() \
    {i++;\
    if (i >= size) {\
      i  = 0;\
      size = gzread(in, buf, sizeof(buf));\
      if (!size) c=0; else c = buf[i];\
    }\
    else c = buf[i];}

inline int File::parse_char() { // a char
  return gzgetc(in);
}

void File::open(std::string nameFile) {
  in = gzopen(nameFile.c_str(), "rb");
  if (in == NULL) {
    std::cout << "*** Error opening file " << nameFile << std::endl;
    std::exit(3);
  }
}

void File::write(std::string nameFile) {
  in = gzopen(nameFile.c_str(), "wb");
  if (in == NULL) {
    std::cout << "*** Error opening file " << nameFile << std::endl;
    std::exit(3);
  }
}

File::~File() {
  gzclose(in);
}

inline bool File::isSpace (char c) {return (c == ' ' || c == '\n' || c == '\r');}

inline const char * File::rChar (char & ch) {  // positive int
  getNext();
  while(isSpace(c)) getNext(); // there could be multiple spaces
  ch = c;
  return 0;
}

inline const char * File::rpint (int &res) {  // positive int
  getNext();
  while(isSpace(c)) getNext(); // there could be multiple spaces
  assert(isdigit (c));
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (INT_MAX / 10 < res || INT_MAX - digit < 10 * res)
      {std::cout << "too large int" << std::endl; std::exit(0);}
    res = 10 * res + digit;
    getNext();
  }
  return 0;
}

// assume all coeffs fit in 'int', and degree fit in 'long long int'
inline const char * File::ruint (uint &res) {
  getNext();
  while(isSpace(c)) getNext(); // there could be multiple spaces
  assert(isdigit(c));
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (UINT_MAX / 10 < res || UINT_MAX - digit < 10 * res)
      {std::cout << "too large uint" << std::endl; exit(0);}
    res = 10 * res + digit;
    getNext();
  }
  return 0;
}
  
inline const char * File::rint (int &res) {
  getNext();
  while(isSpace(c)) getNext(); // there could be multiple spaces
  assert(isdigit(c) or c == '-');
  int sign = 1;
  if (c == '-') {
    getNext();
    if (!isdigit (c)) {std::cout << "expected digit after '-'" << std::endl; exit(0);}
    sign = -1;
  }
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (INT_MAX / 10 < res || INT_MAX - digit < 10 * res) 
      {std::cout << "too large int" << std::endl; exit(0);}
    res = 10 * res + digit;
    getNext();
  }
  res *= sign;
  return 0;
}
  
inline const char * File::rbint (bigint &res) {
  getNext();
  while(isSpace(c)) getNext(); // there could be multiple spaces
  assert(isdigit(c) or c == '-');
  int sign = 1;
  if (c == '-') {
    getNext();
    if (!isdigit (c)) 
      {std::cout << "expected digit after '-'" << std::endl; exit(0);}
    sign = -1;
  }
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    res = 10 * res + digit;
    getNext();
  }
  res *= sign;
  return 0;
}
  
inline const char * File::rLongInt ( long long int &res) {
  getNext();
  while(isSpace(c)) getNext();
  assert(isdigit(c) or c == '-');
  int sign = 1;
  if (c == '-') {
    getNext();
    if (!isdigit (c)) {
      std::cout << "expected digit after '-'" << std::endl; exit(0);}
    sign = -1;
  }
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (LLONG_MAX / 10 < res || LLONG_MAX - digit < 10 * res)
      {std::cout << "too large LONG LONG int" << std::endl; exit(0);}
    res = 10 * res + digit;
    getNext();
  }
  res *= sign;
  return 0;
}

  
inline bool File::rstr (std::string &res) {
  res.clear();
  getNext();
  while(isSpace(c)) getNext();
  while (!isSpace (c)) {res += c; getNext();}
  return (!res.empty());
}
  
inline void File::rbool (bool &res) {
  getNext();
  while(isSpace(c)) getNext();
  res = 1+(c-'1');
  assert((c=='1' && res) or (c == '0' && !res));
  getNext(); assert(isSpace(c));
}

// read from file into queues
void File::readLemma_char(std::string& aux) {
  long long degree;
  int c, orig;
  Lit l;
  if (aux == "l") { // read the core lemmas
    Lemma& lem = solver->lemmas.back();
    while (aux == "l") {
      lem.termsV.push_back(std::vector<Term<int>>());
      auto& terms = lem.termsV.back();
      rint(c); 
      assert(c >= 0 && c < INT_MAX);
      while(c) {rint(l); terms.emplace_back(c, l); rint(c);}
      rLongInt(degree); rint(orig);
      lem.degreeV.push_back(degree); 
      assert(degree <= LLONG_MAX);
      lem.origV.push_back(orig);
      rstr(aux);
    }
  }  
}

// read from file into queues
void File::readCores_char(std::string& aux) {
  assert(aux == "r" or aux == "d"); // results or done
  long long degree;
  int c, orig;
  Lit l;
  if (aux == "r") {
    solver->coreCes.push(CoreCe());
    CoreCe& ce = solver->coreCes.back();
    rint(ce.rDecs);
    rstr(aux); assert(aux == "C");
    while (aux == "C") {
      ce.termsV.push_back(std::vector<Term<int>>());
      auto& terms = ce.termsV.back();
      rint(c); 
      assert(c >= 0 && c < INT_MAX);
      while(c) {rint(l); terms.emplace_back(c, l); rint(c);}
      rLongInt(degree); rint(orig);
      ce.degreeV.push_back(degree);
      assert(degree <= LLONG_MAX);
      ce.origV.push_back(orig);
      rstr(aux);
    }
  }
  if (aux != "d") {std::cout << "read error: aux '" << aux << "' != done, current pos is at INCST, at #confs ?" << std::endl << std::flush;}
  assert(aux == "d");
}


void File::readUntilNextCleanup() {
  assert(solver->lemmas.empty() and solver->allDecisions.empty() and solver->coreCes.empty() and solver->assumpRefs.empty());
  std::string aux;
  char ch;
  long long ctrId;
  int orig;
  int decLit;
  long long degree;
  int c;
  Lit l;
  [[maybe_unused]] int64_t initMem = solver->current_resident_set_size();
  double start = aux::cpuTime();
  while (rstr(aux)) {
    if (aux == "a") {
      rChar(ch);
      solver->assumpRefs.push(ch);
    }
    else if (aux == "F") { // conflict
      rstr(aux); 
      if (aux == "l") { // read a lemma
        solver->lemmas.push(Lemma());
        Lemma& lem = solver->lemmas.back();
        lem.termsV.push_back(std::vector<Term<int>>());
        auto& terms = lem.termsV.back();
        rint(c);
        assert(c >= 0 && c < INT_MAX);
        while(c) {rint(l); terms.emplace_back(c, l); rint(c);}
        rLongInt(degree); rint(orig);
        lem.degreeV.push_back(degree);
        lem.origV.push_back(orig);
      }
      else if (aux == "-1") { // conflict at dl 0
        solver->lemmas.push(Lemma());
      }
      else { // extractCore
        assert(isdigit(aux.c_str()[0])); // 'F' followed by next #conflicts for reading core lemmas
        solver->confCoreLem.push(stoi(aux));
        solver->lemmas.push(Lemma());
        rstr(aux); 
        readLemma_char(aux); // read the core lemmas
        readCores_char(aux);
      }
    }
    else if (isdigit(aux.c_str()[0]) or aux.c_str()[0] == '-') { // no conflict, this is a decision
      decLit = stoi(aux);
      solver->allDecisions.push(decLit);

      if (decLit == 0) { // next 0 
        rstr(aux); assert(aux == "p" or aux == "l" or aux == "r" or aux == "s"); // p->found an unit, l->lemmas learned in extractCore, r->cores, s->solution_found
        solver->direct0s.push(aux.c_str()[0]); 
        assert(solver->direct0s.back() == 'p' or solver->direct0s.back() == 'l' or solver->direct0s.back() == 'r' or solver->direct0s.back() == 's');
        
        if (aux == "l" or aux == "r") {
          solver->lemmas.push(Lemma());
          readLemma_char(aux); // read the core lemmas
          readCores_char(aux);
        }
      }
    }
    else if(aux == "cl") { // clean
      assert(solver->nextCleanupInfo.isReset());
      rint(solver->nextCleanupInfo.trailSize); rLongInt(solver->nextCleanupInfo.nCfReduce);
      rLongInt(ctrId); while(ctrId) {solver->nextCleanupInfo.IDs.emplace_back(ctrId); rLongInt(ctrId);}
      rbool(solver->nextCleanupInfo.GC);
      break;
    }
    else {
      if (aux != "numDecisions:") {std::cout << "reading file error: aux = " << aux << ", it should be 'numDecisions:'" 
        << ", current nDecs " << solver->allDecisions.size() << ", nLems " << solver->lemmas.size() << std::endl; 
      exit(0);}
      
      rLongInt(solver->storedResult.nDecisions); rstr(aux); rLongInt(solver->storedResult.nConflicts); rstr(aux); ruint(solver->storedResult.nSolutionsFound); rstr(aux); ruint(solver->storedResult.nRestarts);
         rstr(aux); ruint(solver->storedResult.nCleanups); rstr(aux); rbint(solver->storedResult.bestCost); rstr(aux); rstr(solver->storedResult.status);
         
      if (solver->storedResult.nDecisions == 0 and solver->storedResult.status == "") {
        std::cout << "There should be some problem in the execution info file, quit!" << std::endl;
        exit(0);
      }
      
      std::cout << "\nFinish reading file \n" << std::flush;
      break;
    }   
  }
  
  double elapsedTime = aux::cpuTime() - start;
  stats.READTIME += elapsedTime;
  solver->memAfterReading = solver->current_resident_set_size();
  std::cout << std::endl << "reading-" << stats.NCLEANUP+1 << " took " << elapsedTime << " s, current mem: " << solver->memAfterReading << ", queue size " << (solver->memAfterReading - initMem) << " MB" << std::endl;
}

}

#include "file.hpp"

  
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
      {cout << "too large uint" << endl; exit(0);}
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
    if (!isdigit (c)) {
      cout << "expected digit after '-'" << endl; exit(0);}
    sign = -1;
  }
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (INT_MAX / 10 < res || INT_MAX - digit < 10 * res)
      {cout << "too large int" << endl; exit(0);}
    res = 10 * res + digit;
    getNext();
  }
  res *= sign;
  return 0;
}

inline const char * File::ruint64 (uint64_t &res) {
  getNext();
  while(isSpace(c)) getNext();
  assert(isdigit(c) or c == '-');
  int sign = 1;
  if (c == '-') {
    getNext();
    if (!isdigit (c)) {
      cout << "expected digit after '-'" << endl; exit(0);}
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
      cout << "expected digit after '-'" << endl; exit(0);}
    sign = -1;
  }
  res = c - '0';
  getNext();
  while (isdigit (c)) {
    int digit = c - '0';
    if (LLONG_MAX / 10 < res || LLONG_MAX - digit < 10 * res)
      {cout << "too large LONG LONG int" << endl; exit(0);}
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

void File::readUntilNextCleanup() {
  assert(solver->lemmas.empty() and solver->allDecisions.empty());
  std::string aux;
  long long ctrId;
  int decLit;
  int c;
  Lit l;
  [[maybe_unused]] int64_t initMem = solver->current_resident_set_size();
  double start = aux::cpuTime();
  
  while (rstr(aux)) {
    if (aux == "F") { // conflict
      solver->lemmas.push(Lemma());
      rint(c);
      if(c != 0) {
        auto& terms = solver->lemmas.back().simCons.terms;
        while(c) {rint(l); terms.emplace_back(c, l); rint(c);}
        rLongInt(solver->lemmas.back().simCons.rhs);
      }
    }
    else if (isdigit(aux.c_str()[0]) or aux.c_str()[0] == '-') { // no conflict
      decLit = stoi(aux);
      solver->allDecisions.push(decLit);
    }
    else if (aux == "cl") { //cleanup
      assert(solver->nextCleanupInfo.isReset());
      rint(solver->nextCleanupInfo.trailSize); rLongInt(solver->nextCleanupInfo.nCfReduce);
      
      rLongInt(ctrId); while(ctrId) {solver->nextCleanupInfo.IDs.push_back(ctrId); rLongInt(ctrId);}
      rbool(solver->nextCleanupInfo.GC);
      break;
    }
    else if(aux == "O") { // obj
      rint(c);
    }
    else {
      if (aux != "numDecisions:") {std::cout << "reading file error: aux = " << aux << ", it should be 'numDecisions:'" 
        << ", current nDecs " << solver->allDecisions.size() << ", nLems " << solver->lemmas.size() << std::endl; 
      exit(0);}
      
      rLongInt(solver->storedResult.nDecisions); rstr(aux); rLongInt(solver->storedResult.nConflicts); rstr(aux); ruint(solver->storedResult.nSolutionsFound); rstr(aux); ruint(solver->storedResult.nRestarts);
         rstr(aux); ruint(solver->storedResult.nCleanups); rstr(aux); rLongInt(solver->storedResult.bestCost); rstr(aux); rstr(solver->storedResult.status);
      
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


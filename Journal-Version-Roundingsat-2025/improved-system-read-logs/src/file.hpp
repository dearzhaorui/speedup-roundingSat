#pragma once

#include <zlib.h>
#include "Solver.hpp"
#include "auxtime.hpp"
#include "globals.hpp"
#include <string>

namespace rs {
  
  class File {
    
    Solver *solver;
    gzFile in;
    char  buf[4096];                          // used by getNext
    uint  i = 0, size = 0;                    // used by getNext
    char  c;                                  // used by getNext
    
   public:
    File (Solver *s, std::string nameFile);
    
    void open (std::string nameFile);
    void write (std::string nameFile);
    void readUntilNextCleanup();
    void readUntilNextCleanup2();
    ~File();
    
   private:
    void getNext();
    bool isSpace (char c);
    const char * rChar (char & ch);
    const char * rpint (int &res);
    const char * rint (int &res);
    const char * rbint (bigint &res);
    const char * ruint (uint &res);
    const char * rLongInt ( long long int &res);
    bool rstr (std::string &res);
    void rbool (bool &res);
    
    int parse_char();
    
    inline void readLemma_char(std::string& aux); // read from file into queues
    inline void readCores_char(std::string& aux); 
  };
  
} //namespace rs

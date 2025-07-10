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

#include "auxtime.hpp"
#include "typedefs.hpp"

namespace rs {

struct Stats {
  
  long long NTRAILPOPS = 0, NWATCHLOOKUPS = 0, NWATCHLOOKUPSBJ = 0, NWATCHCHECKS = 0, NPROPCHECKS = 0,
            NADDEDLITERALS = 0;
  long long NCONFL = 0, NDECIDE = 0, NPROP = 0, NPROPCLAUSE = 0, NPROPCARD = 0, NPROPWATCH = 0, NPROPCOUNTING = 0,
            NRESOLVESTEPS = 0;
  long long NWATCHED = 0, NCOUNTING = 0; 
  long long NWATCHED32 = 0, NWATCHED64 = 0, NWATCHED128 = 0, NWATCHEDARB = 0, NCOUNTING32 = 0, NCOUNTING64 = 0, NCOUNTING128 = 0, NCOUNTINGARB = 0; 
  long long NLOADBINS = 0, NLOADCLAUSES = 0, NLOADCARDS = 0, NLOADPBWATCHED = 0, NLOADPBCOUNTING = 0;
  int128 EXTERNLENGTHSUM = 0, LEARNEDLENGTHSUM = 0;
  int128 PBSLENGTHSUM = 0, CARDSLENGTHSUM = 0, CLAUSESLENGTHSUM = 0, PBSLENGTHSUMINI = 0, CARDSLENGTHSUMINI = 0, CLAUSESLENGTHSUMINI = 0;
  bigint EXTERNDEGREESUM = 0, LEARNEDDEGREESUM = 0;
  long long NCLAUSESEXTERN = 0, NCARDINALITIESEXTERN = 0, NGENERALSEXTERN = 0;
  long long NCLAUSESLEARNED = 0, NCARDINALITIESLEARNED = 0, NGENERALSLEARNED = 0;
  long long NGCD = 0, NCARDDETECT = 0, NCORECARDINALITIES = 0, NCORES = 0, NSOLS = 0;
  long long NWEAKENEDNONIMPLYING = 0, NWEAKENEDNONIMPLIED = 0;
  long long NRESTARTS = 0, NCLEANUP = 0, NGC = 0;
  double STARTTIME = 0, READTIME = 0;
  long long NORIGVARS = 0, NAUXVARS = 0;
  long long NCONSFORMULA = 0, NCONSLEARNED = 0, NCONSBOUND = 0, NCONSCOREGUIDED = 0;
  long long NENCFORMULA = 0, NENCLEARNED = 0, NENCBOUND = 0,
            NENCCOREGUIDED;  // Number of times a reason constraint of this type was encountered.

  long long NLPADDEDROWS = 0, NLPDELETEDROWS = 0;
  long long NLPPIVOTSINTERNAL = 0, NLPPIVOTSROOT = 0, NLPNOPIVOT = 0, NLPRESETBASIS = 0;
  double LPSOLVETIME = 0, LPTOTALTIME = 0;
  long long NLPCALLS = 0, NLPOPTIMAL = 0, NLPINFEAS = 0, NLPFARKAS = 0;
  long long NLPCYCLING = 0, NLPNOPRIMAL = 0, NLPNOFARKAS = 0, NLPSINGULAR = 0, NLPOTHER = 0;
  long long NLPGOMORYCUTS = 0, NLPLEARNEDCUTS = 0, NLPLEARNEDFARKAS = 0, NLPDELETEDCUTS = 0;
  long long NLPENCGOMORY = 0, NLPENCFARKAS = 0,
            NLPENCLEARNEDFARKAS = 0;  // Number of times a reason constraint of this type was encountered.

  long long UNITCORES = 0, SINGLECORES = 0, REMOVEDBLOCKS = 0, FIRSTCOREBEST = 0, DECCOREBEST = 0, NOCOREBEST = 0,
            COREDEGSUM = 0, CORESLACKSUM = 0, COREUBIMPROVE = 0;

  double SOLVETIME = 0, SOLVETIMECG = 0, CATIME = 0, PROPTIME = 0;
  double RUNSTARTTIME = 0;

  inline double getTime() const { return aux::cpuTime() - STARTTIME; }
  inline double getRunTime() const { return aux::cpuTime() - RUNSTARTTIME; }
  inline double getSolveTime() const { return SOLVETIME + SOLVETIMECG; }

  inline long long getDetTime() const {
    return 1 + NADDEDLITERALS + NWATCHLOOKUPS + NWATCHLOOKUPSBJ + NWATCHCHECKS + NPROPCHECKS + NPROP + NTRAILPOPS +
           NDECIDE + NLPPIVOTSROOT + NLPPIVOTSINTERNAL;
  }

  void print() const;
};

}  // namespace rs

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

#include <cmath>
#include "aux.hpp"

struct Stats {
  long long NTRAILPOPS = 0, NWATCHLOOKUPS = 0, NWATCHLOOKUPSBJ = 0, NWATCHCHECKS = 0, NPROPCHECKS = 0,
            NADDEDLITERALS = 0, NADDEDCONSTRAINTS = 0;
  long long NCONFL = 0, NDECIDE = 0, NPROP = 0, NPROPCLAUSE = 0, NPROPCARD = 0, NPROPWATCH = 0, NPROPCOUNTING = 0,
            NRESOLVESTEPS = 0;
  long long NWATCHED = 0, NCOUNTING = 0;
  __int128 EXTERNLENGTHSUM = 0, EXTERNDEGREESUM = 0;
  __int128 LEARNEDLENGTHSUM = 0, LEARNEDDEGREESUM = 0;
  long long NCLAUSESEXTERN = 0, NCARDINALITIESEXTERN = 0, NGENERALSEXTERN = 0;
  long long NCLAUSESLEARNED = 0, NCARDINALITIESLEARNED = 0, NGENERALSLEARNED = 0, NBINLEARNED = 0;
  long long NGCD = 0, NCARDDETECT = 0, NSOLS = 0;
  long long NWEAKENEDNONIMPLYING = 0, NWEAKENEDNONIMPLIED = 0;
  long long NRESTARTS = 0, NCLEANUP = 0, NGC = 0;
  double STARTTIME = 0, READTIME = 0;
  long long NAUXVARS = 0;
  
  int                    startHeightLastDL = 0;
  long long int          numLitsLastDL = 0;
  long long int          numLitsPropagatedLastDL = 0;
  double nPercLastDL = 0, sumPercLastDL = 0;

  double WATCHGEO = 0, WATCHAVG = 0;
  __int128 LENGTHSUM = 0, WATCHSUM = 0;
  
  long long NLOADBINS = 0, NLOADCLAUSES = 0, NLOADCARDS = 0, NLOADPBWATCHED = 0, NLOADPBCOUNTING = 0, NPBWATCHES = 0;
  
  uint nConfsSinceLast = 0, nNoConfsSinceLast = 0;
  uint64_t nWL = 0, sumWL = 0; 
  double nPerc = 0, sumPerc = 0;
  double sumWPerc = 0, sumShortestWPerc = 0;
  

  inline long long getDetTime() const {
    return 1 + NADDEDLITERALS + NWATCHLOOKUPS + NWATCHLOOKUPSBJ + NWATCHCHECKS + NPROPCHECKS + NPROP + NTRAILPOPS +
           NDECIDE;
  }

  void print() const {
    long long totalInput = NCLAUSESEXTERN + NCARDINALITIESEXTERN + NGENERALSEXTERN;
    printf("c input clauses %lld ,( %.2f%s )\n", NCLAUSESEXTERN, (double)NCLAUSESEXTERN / totalInput*100, "%");
    printf("c input cardinalities %lld ,( %.2f%s )\n", NCARDINALITIESEXTERN, (double)NCARDINALITIESEXTERN / totalInput*100, "%");
    printf("c input general constraints %lld ,( %.2f%s )\n", NGENERALSEXTERN, (double)NGENERALSEXTERN / totalInput*100, "%");
    long long nonlearneds = NADDEDCONSTRAINTS - NCONFL;
    printf("c input average constraint length %.2f\n", nonlearneds <= 0 ? 0 : (double)EXTERNLENGTHSUM / nonlearneds);
    printf("c input average constraint degree %.2f\n", nonlearneds <= 0 ? 0 : (double)EXTERNDEGREESUM / nonlearneds);
    long long totalLearned = NCLAUSESLEARNED + NCARDINALITIESLEARNED + NGENERALSLEARNED;
    printf("c learned clauses %lld ,( %.2f%s )\n", NCLAUSESLEARNED, (double)NCLAUSESLEARNED / totalLearned*100, "%");
    printf("c learned cardinalities %lld ,( %.2f%s )\n", NCARDINALITIESLEARNED, (double)NCARDINALITIESLEARNED / totalLearned*100, "%");
    printf("c learned general constraints %lld ,( %.2f%s )\n", NGENERALSLEARNED, (double)NGENERALSLEARNED / totalLearned*100, "%");
    
    printf("c learned average constraint length %.2f\n", NCONFL == 0 ? 0 : (double)LEARNEDLENGTHSUM / NCONFL);
    printf("c learned average constraint degree %.2f\n", NCONFL == 0 ? 0 : (double)LEARNEDDEGREESUM / NCONFL);
    printf("c gcd simplifications %lld\n", NGCD);
    printf("c detected cardinalities %lld\n", NCARDDETECT);
    printf("c weakened non-implied lits %lld\n", NWEAKENEDNONIMPLIED);
    printf("c weakened non-implying lits %lld\n", NWEAKENEDNONIMPLYING);
    printf("c auxiliary variables introduced %lld\n", NAUXVARS);
    printf("c clausal propagations %lld\n", NPROPCLAUSE);
    printf("c cardinality propagations %lld\n", NPROPCARD);
    printf("c watched propagations %lld  ,( %.2f%s )\n", NPROPWATCH, (double)NPROPWATCH / (NPROPWATCH + NPROPCOUNTING)*100, "%");
    printf("c counting propagations %lld  ,( %.2f%s )\n", NPROPCOUNTING, (double)NPROPCOUNTING / (NPROPWATCH + NPROPCOUNTING)*100, "%");
    printf("c propagations %lld\n", NPROP);
    printf("c propagation watch lookups %lld\n", NWATCHLOOKUPS);
    printf("c backjump watch lookups %lld\n", NWATCHLOOKUPSBJ);
    printf("c watch checks %lld\n", NWATCHCHECKS);
    printf("c propagation checks %lld\n", NPROPCHECKS);
    printf("c constraint additions %lld\n", NADDEDLITERALS);
    printf("c trail pops %lld\n", NTRAILPOPS);
    printf("c added constraints %lld\n", NADDEDCONSTRAINTS);
    printf("c total average constraint length %.2f\n",
           NADDEDCONSTRAINTS == 0 ? 0 : (double)LENGTHSUM / (double)NADDEDCONSTRAINTS);
    printf("c total average min watch size %.2f\n",
           NADDEDCONSTRAINTS == 0 ? 0 : (double)WATCHSUM / (double)NADDEDCONSTRAINTS);
    printf("c mean length watch ratio %.2f\n", NADDEDCONSTRAINTS == 0 ? 0 : WATCHAVG / (double)NADDEDCONSTRAINTS);
    printf("c geomean length watch ratio %.2f\n",
           NADDEDCONSTRAINTS == 0 ? 0 : std::exp(WATCHGEO / (double)NADDEDCONSTRAINTS));
    
    printf("c deterministic time %lld %.2e\n", getDetTime(), (double)getDetTime());
    printf("c resolve steps %lld\n", NRESOLVESTEPS);       
    
    printf("\nc watched   constraints %lld ,( %.2f%s ) \n", NWATCHED, (double)NWATCHED / (NWATCHED + NCOUNTING)*100, "%");
    printf("c counting  constraints %lld ,( %.2f%s ) \n", NCOUNTING, (double)NCOUNTING / (NWATCHED + NCOUNTING)*100, "%");
    printf("c loaded bins, clauses, cards, PBs, (WATCH, CTR): %lld , %lld , %lld , %lld ,( %lld , %lld )\n", NLOADBINS, NLOADCLAUSES, NLOADCARDS, (NLOADPBWATCHED+NLOADPBCOUNTING), NLOADPBWATCHED, NLOADPBCOUNTING);
    printf("c NPBWATCHES %lld ,(loadCtr %.2f%s ,loadWatch %.2f%s )\n", NPBWATCHES, (double)NLOADPBCOUNTING / NPBWATCHES*100, "%", (double)NLOADPBWATCHED / NPBWATCHES*100, "%");
    
    printf("\nc decisions %lld\n", NDECIDE);
    printf("c conflicts %lld\n", NCONFL);
    printf("c restarts %lld\n", NRESTARTS);
    printf("c inprocessing phases %lld\n", NCLEANUP);
    printf("c garbage collections %lld ,( %.2f%s )\n", NGC, (double)NGC / NCLEANUP*100, "%");
    
    printf("\nc cpu time %g s\n", aux::cpuTime() - STARTTIME);
    printf("c reading time %g s\n", READTIME);
    printf("c CG solutions found %lld\n", NSOLS);
    
    printf("c AVG.sumWPerc %.2f%s \n", sumWPerc / (NWATCHED + NCOUNTING)*100, "%");
    printf("c AVG.sumShortestWPerc %.2f%s \n", sumShortestWPerc / (NWATCHED + NCOUNTING)*100, "%");
    
    std::cout << "c Avg.WLsize " << (double)sumWL/nWL << " sumWL " << sumWL << " nWL " << nWL << std::endl;
    std::cout << "c Avg.Perc.confWL " << sumPerc/nPerc << "% sumPerc " << sumPerc << " nPerc " << nPerc << std::endl;
    
    std::cout << "\nc Perc.PropLitsLastDL:     " << (double)numLitsPropagatedLastDL/numLitsLastDL*100 << "% ,numLitsPropagatedLastDL " << numLitsPropagatedLastDL << " ,numLitsLastDL " << numLitsLastDL << std::endl;
    std::cout << "c Avg.Perc.PropLitsLastDL: " << sumPercLastDL/nPercLastDL << "% ,sumPercLastDL " << sumPercLastDL << " ,nPercLastDL " << nPercLastDL << std::endl;
    
  }
};

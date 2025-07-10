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

#include "Stats.hpp"

#include <limits>

namespace rs {

/*
void Stats::print() const {  // more clear
    long long nonLearneds = NCLAUSESEXTERN + NCARDINALITIESEXTERN + NGENERALSEXTERN;
    printf("c input clauses %lld ,( %.2f )\n", NCLAUSESEXTERN, (double)NCLAUSESEXTERN/nonLearneds*100);
    printf("c input cardinalities %lld ,( %.2f )\n", NCARDINALITIESEXTERN, (double)NCARDINALITIESEXTERN/nonLearneds*100);
    printf("c input general constraints %lld ,( %.2f )\n", NGENERALSEXTERN, (double)NGENERALSEXTERN/nonLearneds*100);
    printf("c input average constraint length %.2f\n", nonLearneds == 0 ? 0 : (double)EXTERNLENGTHSUM / nonLearneds);
    printf("c input average constraint degree %.2f\n", nonLearneds == 0 ? 0 : (double)EXTERNDEGREESUM / nonLearneds);
    long long learneds = NCLAUSESLEARNED + NCARDINALITIESLEARNED + NGENERALSLEARNED;
    printf("c learned clauses %lld ,( %.2f )\n", NCLAUSESLEARNED, learneds == 0 ? 0 : (double)NCLAUSESLEARNED / learneds*100);
    printf("c learned cardinalities %lld ,( %.2f )\n", NCARDINALITIESLEARNED, learneds == 0 ? 0 : (double)NCARDINALITIESLEARNED / learneds*100);
    printf("c learned general constraints %lld ,( %.2f )\n", NGENERALSLEARNED, learneds == 0 ? 0 : (double)NGENERALSLEARNED / learneds*100);
    printf("c learned average constraint length %.2f\n", learneds == 0 ? 0 : (double)LEARNEDLENGTHSUM / learneds);
    printf("c learned average constraint degree %.2f\n", learneds == 0 ? 0 : (double)LEARNEDDEGREESUM / learneds);
    
    printf("c gcd simplifications %lld\n", NGCD);
    printf("c detected cardinalities %lld\n", NCARDDETECT);
    printf("c original variables %lld\n", NORIGVARS);
    printf("c clausal     propagations %lld\n", NPROPCLAUSE);
    printf("c cardinality propagations %lld\n", NPROPCARD);
    printf("c watched     propagations %lld  ,( %.2f ) \n", NPROPWATCH, (double)NPROPWATCH / (NPROPWATCH + NPROPCOUNTING)*100);
    printf("c counting    propagations %lld  ,( %.2f ) \n", NPROPCOUNTING, (double)NPROPCOUNTING / (NPROPWATCH + NPROPCOUNTING)*100);
    printf("c formula constraints %lld\n", NCONSFORMULA);
    printf("c learned constraints %lld\n", NCONSLEARNED);
    printf("c bound constraints %lld\n", NCONSBOUND);
    printf("c core-guided constraints %lld\n", NCONSCOREGUIDED);
    printf("c CG auxiliary variables introduced %lld\n", NAUXVARS);
    printf("c CG cores constructed %lld\n", NCORES);
    printf("c CG core cardinality constraints returned %lld\n", NCORECARDINALITIES);
    printf("c CG unit cores %lld\n", UNITCORES);
    printf("c CG single cores %lld\n", SINGLECORES);
    printf("c watch checks %lld\n", NWATCHCHECKS);
    printf("c propagation checks %lld\n", NPROPCHECKS);
    printf("c CG core upper bound improvements %lld\n", COREUBIMPROVE);
    
    printf("c resolve steps %lld\n", NRESOLVESTEPS);       
    printf("c propagations %lld\n", NPROP);
    printf("c deterministic time %lld %.2e\n", getDetTime(), (double)getDetTime());
    printf("c optimization time %g s\n", getRunTime() - getSolveTime());  // took for handleInconsistency + handleNewSolution in run.hpp
    printf("\nc total solve time %g s\n", getSolveTime());     // = SOLVETIME + SOLVETIMECG took by solve()
    printf("c core-guided solve time %g s\n", SOLVETIMECG);  // took by solve() when assumps is not empty
    printf("c propagation time %g s\n", PROPTIME);
    printf("c conflict analysis time %g s\n", CATIME);  // took by analyse() + extractCore()
    printf("c watched  CF 32, 64, 128, Arb: %lld , %lld , %lld , %lld\n", NWATCHED32, NWATCHED64, NWATCHED128, NWATCHEDARB);
    printf("c counting CF 32, 64, 128, Arb: %lld , %lld , %lld , %lld\n", NCOUNTING32, NCOUNTING64, NCOUNTING128, NCOUNTINGARB);
    printf("c watched   constraints %lld ,( %.2f ) \n", NWATCHED, (double)NWATCHED / (NWATCHED + NCOUNTING)*100);
    printf("c counting  constraints %lld ,( %.2f ) \n", NCOUNTING, (double)NCOUNTING / (NWATCHED + NCOUNTING)*100);
    printf("c loaded bins, clauses, cards, PBs, (WATCH, CTR): %lld , %lld , %lld , %lld ,( %lld , %lld )\n", NLOADBINS, NLOADCLAUSES, NLOADCARDS, (NLOADPBWATCHED+NLOADPBCOUNTING), NLOADPBWATCHED, NLOADPBCOUNTING);
    
    printf("c average pb length     init %.2f learned %.2f\n", NGENERALSEXTERN == 0 ? 0 : (double)PBSLENGTHSUMINI / NGENERALSEXTERN, NGENERALSLEARNED == 0 ? 0 : (double)PBSLENGTHSUM / NGENERALSLEARNED);
    printf("c average card length   init %.2f learned %.2f\n", NCARDINALITIESEXTERN == 0 ? 0 : (double)CARDSLENGTHSUMINI / NCARDINALITIESEXTERN, NCARDINALITIESLEARNED == 0 ? 0 : (double)CARDSLENGTHSUM / NCARDINALITIESLEARNED);
    printf("c average clause length init %.2f learned %.2f\n", NCLAUSESEXTERN == 0 ? 0 : (double)CLAUSESLENGTHSUMINI/ NCLAUSESEXTERN, NCLAUSESLEARNED == 0 ? 0 : (double)CLAUSESLENGTHSUM / NCLAUSESLEARNED);
    std::cout << "c NPBWATCHES " << NPBWATCHES << " ,perc PBLoads " << (double)(NLOADPBWATCHED+NLOADPBCOUNTING)/NPBWATCHES*100 << "%" << std::endl;
    
    printf("c AVG.sumWPerc %.2f \n", SUMWATCHPERC / (NWATCHED + NCOUNTING)*100);
    printf("c decisions %lld\n", NDECIDE);
    printf("c conflicts %lld\n", NCONFL);
    printf("c restarts %lld\n", NRESTARTS);
    printf("c inprocessing phases %lld\n", NCLEANUP);
    printf("c garbage collections %lld ,( %.2f )\n", NGC, (double)NGC / NCLEANUP*100);
    
    printf("\nc cpu time %g s\n", getTime()); // STARTTIME from main()
    printf("c reading time %g s\n", READTIME);
    
    printf("c CG solutions found %lld\n", NSOLS);
    
  }
*/

    
void Stats::print() const {
    printf("c cpu time %g s\n", getTime());
    printf("c deterministic time %lld %.2e\n", getDetTime(), (double)getDetTime());
    printf("c optimization time %g s\n", getRunTime() - getSolveTime());
    printf("c total solve time %g s\n", getSolveTime());
    printf("c core-guided solve time %g s\n", SOLVETIMECG);
    printf("c propagation time %g s\n", PROPTIME);
    printf("c conflict analysis time %g s\n", CATIME);
    printf("c propagations %lld\n", NPROP);
    printf("c resolve steps %lld\n", NRESOLVESTEPS);
    printf("c decisions %lld\n", NDECIDE);
    printf("c conflicts %lld\n", NCONFL);
    printf("c restarts %lld\n", NRESTARTS);
    printf("c inprocessing phases %lld\n", NCLEANUP);
    printf("c garbage collections %lld ,( %.2f%s )\n", NGC, (double)NGC / NCLEANUP*100, "%");
    
    long long nonLearneds = NCLAUSESEXTERN + NCARDINALITIESEXTERN + NGENERALSEXTERN;
    printf("c input clauses %lld ,( %.2f%s )\n", NCLAUSESEXTERN, (double)NCLAUSESEXTERN/nonLearneds*100, "%");
    printf("c input cardinalities %lld ,( %.2f%s )\n", NCARDINALITIESEXTERN, (double)NCARDINALITIESEXTERN/nonLearneds*100, "%");
    printf("c input general constraints %lld ,( %.2f%s )\n", NGENERALSEXTERN, (double)NGENERALSEXTERN/nonLearneds*100, "%");
    printf("c input average constraint length %.2f\n", nonLearneds == 0 ? 0 : static_cast<double>(EXTERNLENGTHSUM) / nonLearneds);
    
    if (EXTERNDEGREESUM < static_cast<bigint>(std::numeric_limits<double>::max()))
      printf("c input average constraint degree %.2f\n", nonLearneds == 0 ? 0 : static_cast<double>(EXTERNDEGREESUM) / nonLearneds);
    else
      printf("c input average constraint degree inf\n");
    
    long long learneds = NCLAUSESLEARNED + NCARDINALITIESLEARNED + NGENERALSLEARNED;
    printf("c learned clauses %lld ,( %.2f%s )\n", NCLAUSESLEARNED, learneds == 0 ? 0 : (double)NCLAUSESLEARNED / learneds*100, "%");
    printf("c learned cardinalities %lld ,( %.2f%s )\n", NCARDINALITIESLEARNED, learneds == 0 ? 0 : (double)NCARDINALITIESLEARNED / learneds*100, "%");
    printf("c learned general constraints %lld ,( %.2f%s )\n", NGENERALSLEARNED, learneds == 0 ? 0 : (double)NGENERALSLEARNED / learneds*100, "%");
    printf("c learned average constraint length %.2f\n", learneds == 0 ? 0 : static_cast<double>(LEARNEDLENGTHSUM) / learneds);
    
    if (LEARNEDDEGREESUM < static_cast<bigint>(std::numeric_limits<double>::max()))
      printf("c learned average constraint degree %.2f\n", learneds == 0 ? 0 : static_cast<double>(LEARNEDDEGREESUM) / learneds);
    else
      printf("c learned average constraint degree inf\n");
    
    printf("c watched  constraints %lld ,( %.2f%s ) \n", NWATCHED, (double)NWATCHED / (NWATCHED + NCOUNTING)*100, "%");
    printf("c counting constraints %lld ,( %.2f%s ) \n", NCOUNTING, (double)NCOUNTING / (NWATCHED + NCOUNTING)*100, "%");
    printf("c watched  CF 32, 64, 128, Arb: %lld , %lld , %lld , %lld\n", NWATCHED32, NWATCHED64, NWATCHED128, NWATCHEDARB);
    printf("c counting CF 32, 64, 128, Arb: %lld , %lld , %lld , %lld\n", NCOUNTING32, NCOUNTING64, NCOUNTING128, NCOUNTINGARB);
    printf("c loaded clauses, cards, PBs, (WATCH, CTR): %lld , %lld , %lld ,( %lld , %lld )\n", NLOADCLAUSES, NLOADCARDS, (NLOADPBWATCHED+NLOADPBCOUNTING), NLOADPBWATCHED, NLOADPBCOUNTING);
    
    printf("c average pb length     init %.2f ,learned %.2f\n", NGENERALSEXTERN == 0 ? 0 : (double)PBSLENGTHSUMINI / NGENERALSEXTERN, NGENERALSLEARNED == 0 ? 0 : (double)PBSLENGTHSUM / NGENERALSLEARNED);
    printf("c average card length   init %.2f ,learned %.2f\n", NCARDINALITIESEXTERN == 0 ? 0 : (double)CARDSLENGTHSUMINI / NCARDINALITIESEXTERN, NCARDINALITIESLEARNED == 0 ? 0 : (double)CARDSLENGTHSUM / NCARDINALITIESLEARNED);
    printf("c average clause length init %.2f ,learned %.2f\n", NCLAUSESEXTERN == 0 ? 0 : (double)CLAUSESLENGTHSUMINI/ NCLAUSESEXTERN, NCLAUSESLEARNED == 0 ? 0 : (double)CLAUSESLENGTHSUM / NCLAUSESLEARNED);
    
    printf("c gcd simplifications %lld\n", NGCD);
    printf("c detected cardinalities %lld\n", NCARDDETECT);
    printf("c weakened non-implied lits %lld\n", NWEAKENEDNONIMPLIED);
    printf("c weakened non-implying lits %lld\n", NWEAKENEDNONIMPLYING);
    printf("c original variables %lld\n", NORIGVARS);
    printf("c clausal propagations %lld\n", NPROPCLAUSE);
    printf("c cardinality propagations %lld\n", NPROPCARD);
    printf("c watched     propagations %lld  ,( %.2f%s ) \n", NPROPWATCH, (double)NPROPWATCH / (NPROPWATCH + NPROPCOUNTING)*100, "%");
    printf("c counting    propagations %lld  ,( %.2f%s ) \n", NPROPCOUNTING, (double)NPROPCOUNTING / (NPROPWATCH + NPROPCOUNTING)*100, "%");
    printf("c watch lookups %lld\n", NWATCHLOOKUPS);
    printf("c watch backjump lookups %lld\n", NWATCHLOOKUPSBJ);
    printf("c watch checks %lld\n", NWATCHCHECKS);
    printf("c propagation checks %lld\n", NPROPCHECKS);
    printf("c constraint additions %lld\n", NADDEDLITERALS);
    printf("c trail pops %lld\n", NTRAILPOPS);
    printf("c formula constraints %lld\n", NCONSFORMULA);
    printf("c learned constraints %lld\n", NCONSLEARNED);
    printf("c bound constraints %lld\n", NCONSBOUND);
    printf("c core-guided constraints %lld\n", NCONSCOREGUIDED);
    printf("c encountered formula constraints %lld\n", NENCFORMULA);
    printf("c encountered learned constraints %lld\n", NENCLEARNED);
    printf("c encountered bound constraints %lld\n", NENCBOUND);
    printf("c encountered core-guided constraints %lld\n", NENCCOREGUIDED);
    printf("c LP total time %g s\n", LPTOTALTIME);
    printf("c LP solve time %g s\n", LPSOLVETIME);
    printf("c LP constraints added %lld\n", NLPADDEDROWS);
    printf("c LP constraints removed %lld\n", NLPDELETEDROWS);
    printf("c LP pivots internal %lld\n", NLPPIVOTSINTERNAL);
    printf("c LP pivots root %lld\n", NLPPIVOTSROOT);
    printf("c LP calls %lld\n", NLPCALLS);
    printf("c LP optimalities %lld\n", NLPOPTIMAL);
    printf("c LP no pivot count %lld\n", NLPNOPIVOT);
    printf("c LP infeasibilities %lld\n", NLPINFEAS);
    printf("c LP valid Farkas constraints %lld\n", NLPFARKAS);
    printf("c LP learned Farkas constraints %lld\n", NLPLEARNEDFARKAS);
    printf("c LP basis resets %lld\n", NLPRESETBASIS);
    printf("c LP cycling count %lld\n", NLPCYCLING);
    printf("c LP singular count %lld\n", NLPSINGULAR);
    printf("c LP no primal count %lld\n", NLPNOPRIMAL);
    printf("c LP no farkas count %lld\n", NLPNOFARKAS);
    printf("c LP other issue count %lld\n", NLPOTHER);
    printf("c LP Gomory cuts %lld\n", NLPGOMORYCUTS);
    printf("c LP learned cuts %lld\n", NLPLEARNEDCUTS);
    printf("c LP deleted cuts %lld\n", NLPDELETEDCUTS);
    printf("c LP encountered Gomory constraints %lld\n", NLPENCGOMORY);
    printf("c LP encountered Farkas constraints %lld\n", NLPENCFARKAS);
    printf("c LP encountered learned Farkas constraints %lld\n", NLPENCLEARNEDFARKAS);
    printf("c CG auxiliary variables introduced %lld\n", NAUXVARS);
    printf("c CG solutions found %lld\n", NSOLS);
    printf("c CG cores constructed %lld\n", NCORES);
    printf("c CG core cardinality constraints returned %lld\n", NCORECARDINALITIES);
    printf("c CG unit cores %lld\n", UNITCORES);
    printf("c CG single cores %lld\n", SINGLECORES);
    printf("c CG blocks removed during cardinality reduction %lld\n", REMOVEDBLOCKS);
    printf("c CG first core best %lld\n", FIRSTCOREBEST);
    printf("c CG decision core best %lld\n", DECCOREBEST);
    printf("c CG core reduction tie %lld\n", NOCOREBEST);
    printf("c CG core degree average %.2f\n", (NCORES - UNITCORES) == 0 ? 0 : COREDEGSUM / (double)(NCORES - UNITCORES));
    printf("c CG core slack average %.2f\n", (NCORES - UNITCORES) == 0 ? 0 : CORESLACKSUM / (double)(NCORES - UNITCORES));
    printf("c CG core upper bound improvements %lld\n", COREUBIMPROVE);
}

}  // namespace rs

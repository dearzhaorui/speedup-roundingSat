
A Improved Version of RoundingSat Pseudo-Boolean Solver for Speeding Up Propagation
===============================================================================

This repository constains all sources used in the paper "Speeding Up Pseudo-Boolean Propagation". They are built on top of the latest paper version of [RoundingSat Version v2 May 31, 2020](https://zenodo.org/records/3952444) that we can find in the literature which presented rigorous experimental evaluations of different pseudo-Boolean propagation mechanisms.

This improved version of roundingSat uses a novel methodology to precisely assess the performance of counter and watch-based propagation mechanisms presented in the paper. We also carefully evaluated its improved implementation variants leveraging SAT-solver implementers’ knowledge. Finally, we conclude that both propagation routines are very competive and it's strongly suggested to use a hybrid method.

#The `logs` directory containts three example logs that were used in experiments. Each logs include the following main information:
#Decisions, lemmas together with the corresponding backjump level, the restart time and the cleanup time including the lemma identifers to be removed. In addition to the above necessary information, the log file also contains additional information related to each of them for checking the correctness during the solving, such as the number of decisions and conflicts at different solving phases, current decision level, trail size, LBDs, lemma types, the current best solution and the final status. With these information, we can precisely evaluate the performance of different propagation behaviours by avoiding the impact of different search spaces.

The experiments have been done in a cluster with 18 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 3600 seconds.





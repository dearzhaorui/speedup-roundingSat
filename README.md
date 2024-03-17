
A Improved Version of RoundingSat PB Solver for Speeding Up Propagation
===============================================================================

This repository constains all sources used in the paper "Speeding Up Pseudo-Boolean Propagation". They are built on top of the latest [paper](https://dblp.org/rec/conf/cp/Devriendt20.html) version of [RoundingSat Version v2 May 31, 2020](https://zenodo.org/records/3952444) that we can find in the literature which presented rigorous experimental evaluations of different pseudo-Boolean propagation mechanisms.

This improved version of roundingSat uses a novel methodology to precisely assess the performance of counter and watch-based propagation mechanisms presented in the paper. We also carefully evaluated its improved implementation variants with better memory management leveraging SAT-solver implementers’ knowledge. Finally, we conclude that both propagation routines are very comparable and it's strongly suggested to use a hybrid method.

The experiments have been done in a cluster with 10 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 3600 seconds.






A Improved Version of RoundingSat 2025 PB Solver for Speeding Up Propagation
===============================================================================

This repository constains the systems and experiment data used in the article of "Using Execution Logs for Improving Pseudo-Boolean Propagation" in Artificial Intelligence Journal. The article is an extended version of the previous conference paper [[1]](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.22) that integrates some improvements to the unit propagation procedure of RoundingSat 2020 version [[2]](https://link.springer.com/chapter/10.1007/978-3-030-58475-7_10). 

In order to reproduce the results in [2], our work in [1] (the systems and materials can be found in the folder `old-systems-for-SAT2024-paper`) had done the experiments based on the version of code [RoundingSat Version v2 May 31, 2020](https://zenodo.org/records/3952444). In this article we repeated the work and included more improvements based on the same code version on a new benchmark suite selected from the 2024 Pseudo-Boolean Competition. We additionally show
that similar conclusions are reached if the newest available version of RoundingSat is used (June
2025), which combines linear and core-guided search.


This improved version of roundingSat uses a novel methodology to precisely assess the performance of counter and watch-based propagation mechanisms presented in the paper. We also carefully evaluated its improved implementation variants with better memory management leveraging SAT-solver implementers’ knowledge. Finally, we conclude that different propagation routines are suitable for different types of instances and it's strongly suggested to use a hybrid method.

The usage of each system can be found in the individual folders. The experiments have been done in a cluster with 10 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 3600 seconds.


## Reference:

- [1] Improved uint propagation: [Nie+24] Robert Nieuwenhuis, Albert Oliveras, Enric Rodríguez-Carbonell, and Rui Zhao: Speeding up Pseudo-Boolean Propagation. SAT 2024
- [2] Watched propagation: [D20] J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. CP 2020
      

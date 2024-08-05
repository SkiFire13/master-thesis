= Conclusions

We have seen how common systems of fixpoint equations are, especially in model checking, and how we can characterize them using a particular parity game called the powerset game. We have also seen how the moves of this game can be reduced and efficiently expressed using a logic for upward closed sets, which also fits a local algorithm for solving the game. We have then seen a pair of algorithms for solving parity games based on strategies. Our contribution has then been to integrate such algorithm with the powerset game, introducting a series of small optimizations in the process. With this we have improved on a previous attempt of implementing a solver for the powerset game, in some cases even by orders of magnitude.

Although the focus of the game characterization is to be as general as possible, which we have also shown by providing a formulation of bisimilarity using logic formulas, the performance is still quite questionable. Future possibilities would be to explore integration with other parity game algorithms, like the recent quasi-polynomial ones @firstquasipoly @zielonkaquasipoly. The local side of the algorithm could also be improved by extracting more informations from the profiles when performing moves and simplifying formulas, for example expanding an edge could be delayed if it results non-improving, or edges that provide better improvements could be preferred. Another challenge involves integrating up-to techniques in a generic way. Finally, more and exotic domains could be adapted to use this techniques in order to show its generality, for example Łukasiewicz $mu$-calculus @lukamucalculus.

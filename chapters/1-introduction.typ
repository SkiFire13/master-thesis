= Introduction

// Systems of fixpoint equations everywhere in model checking and formal verification
// μ-calculus, bisimilarity, abstract interpretation
// monotone functions, complete lattices (Knaster-Tarski existence, but Kleene infinite)
// characterization via parity games
// cite works
// powerset game (?)
// generalization to specific positions
// known ways to solve 
//
// contribution
// 
// Organization of the rest of the thesis

Systems of mixed least and greatest fixpoint equations over complete lattices are very common in the field of formal analysis and particularly in the field of model checking. A classic example is $mu$-calculus @mucalculus, where liveness and safety properties can be expressed using potentially nested least and greatest fixpoints of functions over sets of states. Behavioral equivalences like many bisimilarities @bisimilarity can also be defined as the greatest fixpoint of an appropriate function over the lattice of the binary relations between states. Another example is Łukasiewicz $mu$-calculus @lukamucalculus, a version of $mu$-calculus which combines deterministic and probabilistic behavior by using continuous functions over the real numbers interval $[0, 1]$. Abstract interpretation @abstractinterpretation also extensively uses fixpoints of functions over functions representing the abstracted state of the program at various points.

It has thus been the focus of many papers in the literature to provide ways to solve fixpoint equations. Most notably the Knaster-Tarski theorem @tarski is a key result for deriving the existence of fixpoints, including the uniqueness of a least and greatest one, while Kleene iteration @kleene gives a constructive way to compute them, albeit generally not very efficient, by repeatedly applying the given function to the bottom or top element. However the mixing of least and greatest fixpoint equations into systems of fixpoint equations, while greatly increasing the expressiveness, also complicates the search for a solution. This is the case for example in the $mu$-calculus, where the use of nested fixpoints is equivalent to a system of mixed least and greatest fixpoint equations.

In this thesis we will build upon the work in @baldan_games and @flori, which provide a way to characterize the solution of a system of mixed fixpoint equations over some complete lattice through the use of an induced parity game, called _powerset game_, which is a kind of game where two players move a token on a directed graph with the winner being decided by the parity of the vertices that are visited. This approach provides a twofold benefit, as it both allows to use existing parity game algorithms to solve the problem, and focuses on specific characteristics of the solution instead of having to compute it in full. Moreover, it has been shown that moves in this game can be expressed by using _symbolic formulas_ in a given logic, which can be exploited to perform simplifications of potentially lot of moves without much work.

Our contribution will then be to adapt some known algorithms @jurdzinski_improvement @friedmann_local to solve the powerset game in a somewhat efficient way, hopefully more than the existing implementation. This will involve performing changes to the powerset game and the algorithms in order to satisfy the assumptions that would otherwise not hold, including requirements on the structure of the graph or how it can be explored. We will give particular attention to the local approach, in order to keep the previously mentioned benefits, and to the simplification of formulas, which can greatly speed up the solver. Our work will also include some optimizations and improvements that became possible thanks to solving this specific kind of game. On top of this we include the translations of some problems to systems of fixpoint equations and the corresponding symbolic formulas, and will solve them using our implementation, comparing the results to the existing work in @flori.

The goal will ultimately be showing that we can solve generic systems of mixed fixpoint equations over some complete lattice, highlighting the flexibility of such approach, and in a way that is faster than the existing approach, though we will not be expecting performance to be necessarily be competitive with state of the art specialized solvers.

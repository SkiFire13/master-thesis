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

Many algorithms have been developed for solving parity game, for our work we have focused mainly on the strategy iteration algorithm @jurdzinski_improvement, which works by iteratively improving a strategy for one player until it becomes optimal according to the related play profiles, and one of its local variants @friedmann_local, which works by solving subgames until it can infer the winner on the full game.

Our main contribution is an adaptation of these algorithms for the powerset game. This involved performing changes both to the powerset game and the local algorithm in order to satisfy some assumptions that would otherwise not hold. For example the strategy iteration algorithm assumes a so called "total" parity game, which the powerset game is not guaranteed to be, so we found a way to convert an arbitrary parity game to a "equivalent" total one, for some definition of "equivalent" we will give. We also generalized the local algorithm to work on subgames defined by a subset of the edges of the full game, rather than a subset of the vertices, due to the powerset game lazily generating those edges. Then we provided a more flexible way to simplify symbolic formulas while keeping track of which generated moves have already been considered, which was needed due to the lazier way we generated such moves. Our work also included some optimizations and improvements that became possible thanks to solving this specific kind of game, for example by computing the play profiles of the current strategy after expanding the subgame, which would otherwise require an expensive step. On top of this we translated some of the previously mentioned problems to systems of fixpoint equations and the corresponding symbolic formulas. These were then solved using our implementation, comparing the results to the existing work in @flori.

The goal will ultimately be showing that we can solve generic systems of mixed fixpoint equations over some complete lattice, highlighting the flexibility of such approach, and in a way that is faster than the existing approach, though we will not be expecting performance to be necessarily be competitive with state of the art specialized solvers.

The rest of this thesis sections are organized as follows:

- @section-background introduces all the theoretical notions which we will build up on. In particular this includes the background needed to introduce systems of fixpoint equations, parity games and the powerset game. It also includes an explanation of $mu$-calculus and bisimilarity, along with a way to convert them to instances we can work with. Finally, it includes descriptions of the parity game algorithms we will be adapting;

- @section-algorithm explains how we adapted the given parity game algorithms to the powerset game and also includes various optimizations that we found for these particular instances;

- @section-implementation presents the implementation of our algorithm, along with its design choices and observations on its performance;

- @section-conclusions summarizes our contribution in this thesis along with possible future improvements or extensions.

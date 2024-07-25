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

Systems of mixed least and greatest fixpoint equations over complete lattices are a very common occurence in the field of formal analysis and particularly model checking. A classic example is $mu$-calculus @mucalculus, where liveness and safety properties can be expressed using potentially nested least and greatest fixpoints of functions over sets of states. Behavioural equivalences like many bisimilarities @bisimilarity can also be defined as the greatest fixpoint of an appropriate function over the lattice of the binary relations betweeen states. Another example is Łukasiewicz $mu$-calculus @lukamucalculus, a version of $mu$-calculus which combines deterministic and probabilistic behavior by using continuous functions over the real numbers interval $[0, 1]$. Astract interpretation @abstractinterpretation also extensively uses fixpoints of functions over functions representing the abstracted state of the program at various points.

It has thus been the focus of many to provide ways to solve fixpoint equations. Most notably Kanster-Tarski's theorem @tarski is a key result for deriving the existance of a solution, while Kleene's iteration @kleene gives a constructive way to compute them, albeit generally not very efficient. However the mixing of least and greatest fixpoint equations, while greatly increasing the expressiveness, also complicates the search for a solution.

In this thesis we will build upon the work in @baldan_games and @flori to characterize the solution of a system of mixed fixpoint equations with an induced parity game, with the goal of adapting some known algorithms @jurdzinski_improvement @friedmann_local to solve them in a somewhat efficient way. The goal will ultimately be solving generalized systems of mixed fixpoint equations, highlighting the flexibility of such approach, though we will not be expecting performance to be necessarily be competitive with state of the art specialized solvers.

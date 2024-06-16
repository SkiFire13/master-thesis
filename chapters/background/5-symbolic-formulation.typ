#import "../../config/common.typ": *

// TODO: Better name? (Characterization?)
== Symbolic formulation and selections

// TODO: Cite Venema. 2008 ?
Systems of fixpoint equations can be characterized using a parity game @baldan_games, also called a powerset game. This characterization in particular allows to determine whether some element of a basis is under the solution for one of the variables of the system. This makes sense because in practice the actual solution of the system may include lot of informations we are not interested about, for example for the $mu$-calculus it would include all the states that satisfy the given formula, while we are only interested in knowing whether one particular state is included, or for bisimilarity it would include all pairs of processes that are bisimilar, but again we are only interested in a single pair.

// TODO: Intuition on the definition?

#definition("powerset game")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Let $E = tup(x) feq_tup(eta) tup(f) (tup(x))$ be a system of $n$ fixpoint equations.

  The powerset game is a parity game associated with $E$ defined as:

  - the vertices for player 0 are $V_0 = B_L times range(n) = { (b, i) | b in B_L and i in range(n) }$
  
  - the vertices for player 1 are $V_1 = (2^(B_L))^n = { (X_1, ..., X_n) | X_i in 2^(B_L) }$

  - the moves from player 0 vertices are $E(b, i) = { tup(X) | tup(X) in (2^(B_L))^n and b sub f_i (join tup(X)) }$

  - the moves from player 1 vertices are $A(tup(X)) = { (b, i) | i in range(n) and b in X_i }$

  - the priority function is defined such that:
    
    - $p(tup(X)) = 0$;

    - $p((b, i))$ is even if $eta_i = nu$ and odd if $eta_i = mu$;

    - $p((b, i)) < p((b', j))$ if $i < j$.
]

The given priority function is not fully specified, but it can be shown that there exist a mapping to $bb(N)$ that satisfies the given order and partition into even/odd. An intuitive way would be to just list the priorities in order and give to map each of them to the next available even or odd natural number.

// TODO: Cite Venema. 2008 ?
// TODO: theorem?
#lemma("correctness and completeness of the powerset game")[
  Let $E$ be a system of $n$ fixpoint equations over a complete lattice $L$ with solution $s$. For all $b in B_L$ and $i in range(n)$, we have $b sub s_i$ if and only if the player 0 has a winning strategy on the powerset game associated to $E$ starting from the vertex $(b, i)$.
]

// TODO: ref to paper proving this.

// TODO: Example ?


// TODO for selections:
//  - selection
//  - upward closure
//  - hoare preorder
//  - least selection
//  - logic for upward closed sets
//  - symbolic moves
//  - composition of moves (mention?)

// Alternative:
//  - skip selection
//  - observation that some moves are useless
//  - minimal set of moves not always possible
//  - symbolic moves

// Selection
// Selections are equivalent (no proof)
// Symbolic moves
// Symbolic moves are representation of all possible moves
// Symbolic moves are a selection

In practice it is not convenient to consider all the possible moves for player 0. Consider for example two moves for player 0 that lead to the positions $tup(X)$ and $tup(Y)$ for player 1. If $A(tup(X)) subset A(tup(Y))$ then intuitively $tup(Y)$ is never convenient for player 0, as it will give player 1 strictly move moves to play and thus more chances to win.

TODO: define selection

TODO: restricting strategies to ones consistent with selection preserves winner

TODO: Informal introduction to logic

// TODO: ref to symbolic moves paper

#definition("logic for symbolic moves")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Given $n in bb(N)$ we can define the following logic, where $b in B_L$ and $i in range(n)$:

  $
    phi := [b, i] | and.big_(k in K) phi_k | or.big_(k in K) phi_k
  $
]

#definition("semantic of symbolic moves")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula for symbolic moves. The semantics of the formula $phi$, that is the set of player 1 vertices is represents, are:
  #let sem(of) = $bracket.l.double of bracket.r.double$
  $
    sem([b, i]) &= { tup(X) | b in tup(X)_i } \
    sem(and.big_(k in K) phi_k) &= sect.big_(k in K) sem(phi_k) \
    sem(or.big_(k in K) phi_k) &= union.big_(k in K) sem(phi_k)
  $
]

#definition("generator for symbolic moves")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula for symbolic moves. We can define the following generator of reduced moves for player 0:

  $
    M([b, i]) &= { tup(X) } "with" X_i = { b } "and" forall j != i. X_j = emptyset \
    // TODO: Is this simplified version correct?
    M\(and.big_(k in K) phi_k\) &= { union.big X | X in product_(k in K) M(phi_k) } \
    M\(or.big_(k in K) phi_k\) &= union.big_(k in K) M(phi_k)
  $
]

// TODO: Comment, example?
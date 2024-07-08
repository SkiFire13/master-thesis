#import "../../config/common.typ": *

== Game characterization

=== Game definition

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
It has been proven in @baldan_games that such characterization is both correct and complete, allowing us to solve generic systems of fixpoint equations with it.

#theorem("correctness and completeness of the powerset game")[
  Let $E$ be a system of $n$ fixpoint equations over a complete lattice $L$ with solution $s$. For all $b in B_L$ and $i in range(n)$, we have $b sub s_i$ if and only if the player 0 has a winning strategy on the powerset game associated to $E$ starting from the vertex $(b, i)$.
]

=== Selections

// TODO: Better examples
// TODO: Citations
In practice it is not convenient to consider all the possible moves for player 0. Consider for example two moves for player 0 that lead to the positions $tup(X)$ and $tup(Y)$ for player 1. If $A(tup(X)) subset A(tup(Y))$ then intuitively $tup(Y)$ is not convenient for player 0, as it will give player 1 strictly more moves to play and thus more chances to win. We will now see a formalization of this idea.

// TODO: Cite where this was first defined
To start we will need to define a new order, called _Hoare preorder_:

#definition("Hoare preorder")[
  Let $(P, sub)$ be a poset. The Hoare preorder, written $hsub$, is a preorder on the set $2^P$ such that, $forall X, Y subset.eq P. X hsub Y <=> forall x in X. exists y in Y. x sub y$.
]

We also consider the pointwise extension $phsub$ of the Hoare preorder on the set $(2^(B_L))^n$, that is $forall X, Y in (2^(B_L))^n, tup(X) phsub tup(Y) <=> forall i in range(n). X_i hsub Y_i$, and the upward-closure with respect to it, that is given $T subset.eq (2^(B_L))^n$ then $up_H T = { tup(X) | exists tup(Y) in T and tup(Y) phsub tup(X) }$.

The idea will then be for player 0 to avoid playing a move $tup(Y)$ if there exist another move $tup(X)$ such that $tup(X) phsub tup(Y)$. More formally we consider _selections_ of moves, that is subsets of moves that are equivalent to the full set for the purpose of the game.

#definition("selection")[
  Let $(L, sub)$ be a lattice. A selection is a function $sigma : (B_L times range(n)) -> 2^((2^(B_L))^m)$ such that $forall b in B_L, i in range(n). up_H sigma(b, i) = E(b, i)$.
]

// TODO: Cite where this was proven
It can be proven that a selection always exists and is $E(b, i)$. Moreover it can be proven that the winner of a game where player 0's moves are replaced with a selection is the same as the winner in the original game. This allows us to soundly use a selection as an alternative set of moves for player 0, which is possibly smaller than the original one.

=== Logic for upward-closed sets

Ideally we would be interested in the least selection; this can be shown to always exist in finite lattices, but not in infinite ones. However the least selection can be exponential with respect to the basis size; for this reason a logic for upward-closed sets is used to represent the $E(b, i)$ set in a compact way. Additionally this allows us to generate sets of moves which are typically small, even if they are not the least ones. 
// TODO(Prof): "since not compositional"?

#definition("logic for upward-closed sets")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Given $n in bb(N)$ we can define the following logic, where $b in B_L$ and $i in range(n)$:

  $
    phi := [b, i] | and.big_(k in K) phi_k | or.big_(k in K) phi_k
  $
]

The true and false formula are then implicitly defined as $and_(k in emptyset) phi_k$ and $or_(k in emptyset) phi_k$.

#definition("logic formulas semantics")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula. The semantics of $phi$, that is the set of player 1 vertices is represents, is a upward-closed set $sem(phi) subset.eq (2^(B_L))^n$ with respect to $phsub$, define as:
  $
    sem([b, i]) &= { tup(X) | b in tup(X)_i } \
    sem(and.big_(k in K) phi_k) &= sect.big_(k in K) sem(phi_k) \
    sem(or.big_(k in K) phi_k) &= union.big_(k in K) sem(phi_k)
  $
]

// TODO: Composition of moves, system of equations, etc etc?
#definition("generator for symbolic moves")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula. The moves generated by $phi$, written $M(phi)$ are:

  $
    M([b, i]) &= { tup(X) } "with" X_i = { b } "and" forall j != i. X_j = emptyset \
    // TODO: Is this simplified version correct?
    M\(and.big_(k in K) phi_k\) &= { union.big X | X in product_(k in K) M(phi_k) } \
    M\(or.big_(k in K) phi_k\) &= union.big_(k in K) M(phi_k)
  $
]

Another advantage of using such formulas is that they can be simplified when it becomes known that some position for player 0 is winning or losing. Such simplification would be done by replacing the corresponding $[b, i]$ atom in the formula to respectively true or false. In the parity game this would then translate to either removing a set of moves for player 0, corresponding to those that allow player 1 to reach a winning position for them, or replacing moves for player 0 with ones without moves that are immediately losing for player 1.

// TODO: Comment, example?

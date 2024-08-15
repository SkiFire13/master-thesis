#import "../../config/common.typ": *

== Game characterization

=== Game definition

// TODO: Cite Venema. 2008 ?
Systems of fixpoint equations can be characterized using a parity game @baldan_games, also called a powerset game. This characterization in particular allows to determine whether some element of a basis is under the solution for one of the variables of the system. This makes sense because in practice the actual solution of the system may include lot of informations we are not interested about, for example for the $mu$-calculus it would include all the states that satisfy the given formula, while we are only interested in knowing whether one particular state is included, or for bisimilarity it would include all pairs of processes that are bisimilar, but again we are only interested in a single pair.

// TODO: Intuition on the definition?

#definition("powerset game")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Let $E = tup(x) feq_tup(eta) tup(f) (tup(x))$ be a system of $n$ fixpoint equations.

  The powerset game is a parity game associated with $E$ defined as follows:

  - the vertices for player 0 are $V_0 = B_L times range(n) = { (b, i) | b in B_L and i in range(n) }$
  
  - the vertices for player 1 are $V_1 = (2^(B_L))^n = { (X_1, ..., X_n) | X_i in 2^(B_L) }$

  - the moves from player 0 vertices are $E(b, i) = { tup(X) | tup(X) in (2^(B_L))^n and b sub f_i (join tup(X)) }$

  - the moves from player 1 vertices are $A(tup(X)) = { (b, i) | i in range(n) and b in X_i }$

  - the priority function is defined such that:
    
    - $p(tup(X)) = 0$;

    - $p((b, i))$ is even if $eta_i = nu$ and odd if $eta_i = mu$;

    - $p((b, i)) < p((b', j))$ if $i < j$.
]

Intuitively each player 0 vertex $(b, i)$ represents the fact that the basis element $b$ is under the final solution for the variable $x_i$. Its moves then are all the possible assignments to the tuple of variables $tup(x)$, expressed however as tuples of subsets of the basis, such that $b$ is under the result of $f_i (tup(x))$. Player 1 then can challenge player 0 by claiming that one of those subsets contains an element of the basis that is not actually under the solution, and this continues either infinitely or until one of the two players has no move possible.

The given priority function is not fully specified, but it can be shown that there exist a mapping to $bb(N)$ that satisfies the given order and partition into even/odd. An intuitive way would be to just list the priorities in order and give to map each of them to the next available even or odd natural number.

// TODO: Cite Venema. 2008 ?
It has been proven in @baldan_games that such characterization is both correct and complete, allowing us to solve generic systems of fixpoint equations with it.

#theorem("correctness and completeness of the powerset game")[
  Let $E$ be a system of $n$ fixpoint equations over a complete lattice $L$ with solution $s$. For all $b in B_L$ and $i in range(n)$, we have $b sub s_i$ if and only if the player 0 has a winning strategy on the powerset game associated to $E$ starting from the vertex $(b, i)$.
]

// TODO: Example of (small) powerset game?

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
It can be proven that a selection always exists and is $E(b, i)$. Moreover it can be proven that the winner of a game where player 0 moves are replaced with a selection is the same as the winner in the original game. This allows us to soundly use a selection as an alternative set of moves for player 0, which is possibly smaller than the original one.

=== Logic for upward-closed sets

Ideally we would be interested in the least selection; this can be shown to always exist in finite lattices, but not in infinite ones. Consider for example the complete lattice based on the set of natural numbers extended with the top element $omega$ seen in the center of @lattice-example, and consider a system of fixpoint equations with only the equation $x feq_mu f(x)$ where $f(n) = n + 1$ if $n in bb(N)$ and $f(omega) = omega$. We will pick the lattice itself as its basis and we will want to prove $omega sub x^*$ with $x^*$ being the solution of this equation. This will generate a powerset game starting from position $omega$ with moves $E(omega)$, for which it can be shown that the move $bb(N)$ is winning for player 0. We are however interested in selections for $E(omega)$, and it can be shown that any ${ X }$ where $X subset.eq bb(N)$ and $X$ is infinite is a valid selection for $E(omega)$. In fact $omega sub f(join X)$ can only be satisfied if $f(join X) = omega$ and thus $join X = omega$, which is true for any infinite $X$. There are however infinite such sets, and there is no smallest one, since it is always possible to get a smaller one by removing one element. Thus there cannot be a smallest selection.

Moreover the least selection can be exponential with respect to the number of variables and basis size. Take for example the function $f(x_1, ..., x_(2n)) = (x_1 or x_2) and (x_3 or x_4) and ... and (x_(2n-1) or x_(2n))$ over the boolean lattice. The corresponding minimal selection would be ${ ({tt}, varempty, {tt}, varempty, ...), ..., (varempty, {tt}, varempty, {tt}, ...) }$, which lists all the ways to satisfy each $x_(2i-1) or x_(2i)$ without making them both $tt$, which is $2^n$ and thus exponential in the number of variables. A similar construction can be made for the basis size, by taking as domain the set of $n$-tuples over the boolean lattice.

For these reasons a logic for upward-closed sets is used to represent the $E(b, i)$ set in a compact way. Additionally this allows us to generate sets of moves which are typically small, even if they are not the least ones. From now on we will refer to formulas in such logic with "logic formulas".
// TODO(Prof): "since not compositional"?

// TODO: Example least selection is exponential

#definition("logic for upward-closed sets")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Given $n in bb(N)$ we can define the following logic, where $b in B_L$ and $i in range(n)$:

  $
    phi := [b, i] | and.big_(k in K) phi_k | or.big_(k in K) phi_k
  $
]

The $tt$ and $ff$ formula are then implicitly defined as $and_(k in varempty) phi_k$ and $or_(k in varempty) phi_k$.

#definition("logic formulas semantics")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula. The semantics of $phi$, that is the set of player 1 vertices is represents, is a upward-closed set $sem(phi) subset.eq (2^(B_L))^n$ with respect to $phsub$, define as follows:
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
    M([b, i]) &= { tup(X) } "with" X_i = { b } "and" forall j != i. X_j = varempty \
    // TODO: Is this simplified version correct?
    M\(and.big_(k in K) phi_k\) &= { union.big X | X in product_(k in K) M(phi_k) } \
    M\(or.big_(k in K) phi_k\) &= union.big_(k in K) M(phi_k)
  $
]

Another advantage of representing selections using such formulas is that they can be simplified when it becomes known that some position for player 0 is winning or losing. Such simplification would be done by replacing the corresponding $[b, i]$ atom in the formula to respectively true or false. In the parity game this would then translate to either removing a set of moves for player 0, corresponding to those that allow player 1 to reach a winning position for them, or replacing moves for player 0 with ones without moves that are immediately losing for player 1.

It should be noted however that we cannot automatically get such formulas from any opaque function that could appear in a system of fixpoint equations. Instead, this will need to be done separately for each function, or class of functions.

// TODO: Comment, example?

=== Translating $mu$-calculus formulas <mucalculus-translation>

As seen in @mucalculus-application, $mu$-calculus formulas can be translated into systems of fixpoint equations. The functions appearing in such systems can also be automatically translated into logic formulas for upward-closed sets. Consider a system of fixpoint equations generated by a $mu$-calculus formula:

$
    syseq(
    x_1 &feq_eta_1 phi_1 (x_1, ..., x_n) \
    &#h(0.3em)dots.v \
    x_n &feq_eta_n phi_n (x_1, ..., n_n) \
  )
$

We need to define a logic formula representing the moves for player 0 for each vertex $(b, i)$ for a basis element $b$ and a variable index $i$. Recall that the system of equations is defined over $2^bb(S)$, the powerset lattice of its states, and whose basis is $bb(S)$ as shown in @powerset-basis. We thus need to define a formula for each state $s$ and index $i$ such that the formula is true when the state $s$ satisfies the formula $phi_i (tup(x^*))$, with $tup(x^*)$ representing the actual solution of the system. Moreover we are allowed to refer to any vertex controlled by player 0 in this formula, which is equivalent to being able to require that any another state $s'$ satisfies one of the formulas $phi_j (tup(x^*))$.

We can then define the logic formula for the vertex $(s, i)$ as $F(s, phi_i (x_1, ..., x_n))$, where $F$ is in turn defined by structural induction on its second argument:

#eq-columns(
  $
    F(s, tt) &= tt \
    F(s, ff) &= ff \
    F(s, p) &= cases(
      tt & "if" s in rho_0(p) \
      ff & "if" s in.not rho_0(p)
    ) \
    F(s, psi_1 or psi_2) &= F(s, psi_1) or F(s, psi_2) \
  $,
  $
    F(s, x_i) &= [b, i] \
    F(s, diam(A) psi) &= and.big_(a in sem(A)) and.big_(s ->^a t) F(t, psi) \
    F(s, boxx(A) psi) &= or.big_(a in sem(A)) or.big_(s ->^a t) F(t, psi) \
    F(s, psi_1 and psi_2) &= F(s, psi_1) and F(s, psi_2) \
  $
)

// TODO: This should use composition of operators?
It is interesting to note that the cases for $diam(A) psi$ and $boxx(A) psi$ are effectively taking the respective semantics definition, which use universal and existential equantifiers, and translating them to finite sequence of respectively conjunctions and disjunctions between the elements that satisfy such quantifiers.

The definition also did not include fixpoint formulas since those were already been removed when translating to a system of fixpoint equations.

// TODO: Example of logic formulas for mucalculus?

=== Translating bisimilarity

Likewise for bisimilarity we have seen in @bisimilarity-application that it can be translated to a fixpoint equation, which in turn can be seen as a system of a single fixpoint equation. As with $mu$-calculus formulas the domain is the powerset lattice $2^(bb(S) times bb(S))$, and thus its basis is $bb(S) times bb(S)$. Since there is just one variable and equation we will only define $F(s_1, s_2)$, representing the formula for the player 0 vertex $((s_1, s_2), 1)$:

$
  F(s_1, s_2) =
    (
      (and.big_(a in Act) and.big_(s_1 ->^a t_1) or.big_(s_2 ->^a t_2) [(t_1, t_2), 1])
      and
      (and.big_(a in Act) and.big_(s_2 ->^a t_2) or.big_(s_1 ->^a t_1) [(t_1, t_2), 1])
    )
$

For example the formulas for the pair of states in the labelled transition systems shown in @bisimilarity-example are the following:

$
  F(v_0, u_0) &= ([(v_1, u_1), 1] and [(v_2, u_1), 1]) and ([(v_1, u_1), 1] or [(v_2, u_1), 1]) \
    &= [(v_1, u_1), 1] and [(v_2, u_1), 1] \
  F(v_0, u_1) &= ff and ff = ff \
  F(v_0, u_2) &= ff and tt = ff \
  #v(0em) \
  F(v_1, u_0) &= ff and ff = ff \
  F(v_1, u_1) &= [(v_3, u_2), 1] and [(v_3, u_2), 1] = [(v_3, u_2), 1] \
  F(v_1, u_2) &= ff and tt = ff \
  #v(0em) \
  F(v_2, u_0) &= ff and ff = ff \
  F(v_2, u_1) &= [(v_3, u_2), 1] and [(v_3, u_2), 1] = [(v_3, u_2), 1] \
  F(v_2, u_2) &= ff and tt = ff \
  #v(0em) \
  F(v_3, u_0) &= tt and ff = ff \
  F(v_3, u_1) &= tt and ff = ff \
  F(v_3, u_2) &= tt and tt = tt
$

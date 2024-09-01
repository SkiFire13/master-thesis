#import "../../config/common.typ": *
#import "@preview/cetz:0.2.2": canvas, draw, vector

== Game characterization of the solution of systems of equations

=== Game definition

The solution of systems of fixpoint equations can be characterized using a parity game @baldan_games, also called a powerset game. This characterization in particular allows to determine whether some element of a basis is under the solution for one of the variables of the system. This makes sense because in practice the actual solution of the system may include lot of informations we are not interested about, for example for the $mu$-calculus it would include all the states that satisfy the given formula, while we might be only interested in knowing whether one particular state is included, or for bisimilarity it would include all pairs of processes that are bisimilar, when again we are only interested in a single pair.

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

Intuitively each vertex $(b, i)$, owned by player 0, represents the fact that the basis element $b$ is under the $i$-th component of the solution. Its moves then are all the possible assignments to the tuple of variables $tup(x)$. These are expressed as tuples of subsets $X_1, ..., X_n$ of the basis, with the requirement that $b$ is under the result of $f_i (join X_1, ..., join X_n)$. Player 1 then can challenge player 0 by claiming that one of those subsets contains an element of the basis that is not actually under the solution, and this continues either infinitely or until one of the two players has no move possible.

The priority function is not fully specified, but it can be shown that there exist a mapping to $bb(N)$ that satisfies the given order and partition into even/odd. An intuitive way would be to just list the priorities in order and give to map each of them to the next available even or odd natural number.

It has been proven in @baldan_games that such characterization is both correct and complete, allowing us to solve generic systems of fixpoint equations with it.

#theorem("correctness and completeness of the powerset game")[
  Let $E$ be a system of $n$ fixpoint equations over a complete lattice $L$ with solution $s$. For all $b in B_L$ and $i in range(n)$, we have $b sub s_i$ if and only if the player 0 has a winning strategy on the powerset game associated to $E$ starting from the vertex $(b, i)$.
]

#example("game characterization", label: <game-ch-example>)[
  Consider for example the system of equations given in @system-example over the boolean lattice $bb(B)$:
  
  $
    syseq(
      x_1 &feq_mu x_1 or x_2 \
      x_2 &feq_nu x_1 and x_2 \ 
    )
  $

  The corresponding game characterization would be the following:

  #let game_example(withstrategy) = canvas({
    import draw: *

    set-style(content: (padding: .2), stroke: black)

    let node(pos, name, p, label, pr) = {
      let cname = name + "content"
      content(pos, label, name: cname, padding: 1em)
      if p == 0 {
        circle(pos, name: name, radius: (1, 0.65), stroke: black)
        content((v => vector.add(v, (0, .16)), cname + ".south"), text(str(pr)))
      } else {
        let (x, y) = pos
        rect(cname + ".north-west", cname + ".south-east", name: name, radius: 0.05)
        content((v => vector.add(v, (-.2, .2)), cname + ".south-east"), text(str(pr)))
      }
    }

    node((4.5, 0), "t1", 0, $[tt, 1]$, 1)
    node((4.5, -2.5), "t2", 0, $[tt, 2]$, 2)
    
    node((0, 0), "tt_e", 1, $({tt}, varempty)$, 0)
    node((0, -2.5), "e_tt", 1, $(varempty, {tt})$, 0)
    node((10, -1.25), "tt_tt", 1, $({tt}, {tt})$, 0)

    let edge(ni, ai, nf, af, a, w) = {
      let pi = (name: ni, anchor: ai)
      let pf = (name: nf, anchor: af)
      let c = if withstrategy and not w { (dash: "dotted") } else { black }
      bezier(pi, pf, (pi, 50%, a, pf), fill: none, stroke: c, mark: (end: ">"))
    }

    edge("t1", 160deg, "tt_e", 20deg, -20deg, false)
    edge("t1", 240deg, "e_tt", 20deg, 20deg, true)
    edge("t1", 20deg, "tt_tt", 130deg, 20deg, false)

    edge("t2", -20deg, "tt_tt", -130deg, -20deg, true)

    edge("tt_e", -20deg, "t1", 200deg, -20deg, false)
    edge("e_tt", -20deg, "t2", 200deg, -20deg, false)
    edge("tt_tt", 160deg, "t1", -20deg, 20deg, false)
    edge("tt_tt", 200deg, "t2", 20deg, -20deg, false)
  })

  #figure(
    game_example(true),
    caption: [Example of a game characterization],
  ) <game-example>

  As before, elliptic vertices represent player 0 positions while rectangular vertices represent player 1 positions. The priorities are now represented with the numbers on the bottom center or right, while the non-dotted edges correspond to the winning strategies.

  The way this is obtained is by starting with the player 0 positions, which are the ones we care about, since if one wanted to prove whether $tt$ is under the solution for $x_1$ or $x_2$ they would have to check whether $[tt, 1]$ or $[tt, 2]$ are winning or not. From those vertices we then have the following moves:

  $
    E(tt, 1) &= { #h(0.3em) ({tt}, varempty), #h(0.6em) (varempty, {tt}), #h(0.6em) ({tt}, {tt}) #h(0.3em) } \
    E(tt, 2) &= { #h(0.3em) ({tt}, {tt}) #h(0.3em) }
  $

  Note that the remaining position of player 1 $(varempty, varempty)$ is not reachable, and thus was omitted from the figure.

  The game is ultimately won by player 0 on every position, since it can force every play to go through the position $[tt, 2]$ over and over. This position has the highest priority, at 2, thus being the highest of every play, and since it is even it makes player 0 the winner. Hence we can infer that $tt sub x^*_1$ and $tt sub x^*_2$, which implies $x^*_1 = tt$ and $x^*_2 = tt$.

  One can also see that swapping the equations would result in the same parity graph, except for position $[tt, 1]$ which now would have a higher odd priority than $[tt, 2]$. This makes the game losing for player 0 on all positions, since player 1 can force every play to go through $[tt, 1]$ and win. We thus get $tt subn x^*_1$ and $tt subn x^*_2$, which imply $x^*_1 = ff$ and $x^*_2 = ff$, like we already saw in @order-equations.
]

=== Selections

In practice it is not convenient to consider all the possible moves for player 0. For instance in @game-ch-example the move from $[tt, 1]$ to $({tt}, {tt})$ is never convenient for player 0, since the moves to $({tt}, varempty)$ and $(varempty, {tt})$ would give player 1 strictly less choices. In fact going from $[tt, 2]$ to $({tt}, {tt})$ would be a losing move for player 0, and the only way to win is to go to $(varempty, {tt})$. In general, for player 0, it will be always convenient to play moves consisting of sets of elements with limited cardinality and as small as possible in the order. We will now see a formalization of this idea.

// TODO: Cite where this was first defined
To start we will need to consider a new order, called _Hoare preorder_:

#definition("Hoare preorder")[
  Let $(P, sub)$ be a poset. The Hoare preorder, written $hsub$, is a preorder on the set $2^P$ such that, $forall X, Y subset.eq P. X hsub Y <=> forall x in X. exists y in Y. x sub y$.
]

We also consider the pointwise extension $phsub$ of the Hoare preorder on the set $(2^(B_L))^n$, that is $forall X, Y in (2^(B_L))^n, tup(X) phsub tup(Y) <=> forall i in range(n). X_i hsub Y_i$, and the upward-closure with respect to it, that is given $T subset.eq (2^(B_L))^n$ then $up_H T = { tup(X) | exists tup(Y) in T and tup(Y) phsub tup(X) }$.

The idea will then be for player 0 to avoid playing a move $tup(Y)$ if there exist another move $tup(X)$ such that $tup(X) phsublt tup(Y)$. More formally, it can be proven that any set of moves whose upward-closure with respect to $phsub$ is equal to $E(b, i)$ is equivalent to it for the purpose of the game. That is, we can replace the moves for that player 0 position and it would not change the winners compared to the original game. We call such sets of moves _selections_, and a point of interest will be finding small selections in order to reduce the size of the game.

#definition("selection")[
  Let $(L, sub)$ be a lattice. A selection is a function $sigma : (B_L times range(n)) -> 2^((2^(B_L))^m)$ such that $forall b in B_L, i in range(n). up_H sigma(b, i) = E(b, i)$.
]

=== Logic for upward-closed sets <upward-logic>

Ideally we would be interested in the least selection; this can be shown to always exist in finite lattices, but not in infinite ones. Moreover when it exists it might be exponential in size.

#example("least selection may not exist")[
  Consider for example the complete lattice $bb(N)_omega$ seen in @poset-example, and consider a system of fixpoint equations with only the equation $x feq_mu f(x)$ where $f(n) = n + 1$ if $n in bb(N)$ and $f(omega) = omega$. We will pick the lattice itself as its basis and we will want to prove $omega sub x^*$ with $x^*$ being the solution of this equation. This will generate a powerset game starting from position $omega$ with moves $E(omega)$, for which it can be shown that the move $bb(N)$ is winning for player 0. We are however interested in selections for $E(omega)$, and it can be shown that any ${ X }$ where $X subset.eq bb(N)$ and $X$ is infinite is a valid selection for $E(omega)$. In fact $omega sub f(join X)$ can only be satisfied if $f(join X) = omega$ and thus $join X = omega$, which is true for all and only the infinite $X$. There are however infinitely many such sets, and there is no smallest one, since it is always possible to get a smaller one by removing one element. Thus there cannot be a smallest selection.
]

#example("least selection can be exponential")[
  The least selection can be exponential with respect to the number of variables and basis size. Take for example the function $f(x_1, ..., x_(2n)) = (x_1 or x_2) and (x_3 or x_4) and ... and (x_(2n-1) or x_(2n))$ over the boolean lattice. The corresponding minimal selection would be ${ ({tt}, varempty, {tt}, varempty, ...), ..., (varempty, {tt}, varempty, {tt}, ...) }$, which lists all the ways to satisfy each $x_(2i-1) or x_(2i)$ without making them both $tt$, which is $2^n$ and thus exponential in the number of variables. A similar construction can be made for the basis size, by taking as domain the set of $n$-tuples over the boolean lattice.
]

For these reasons a logic for upward-closed sets is used to represent the $E(b, i)$ set in a more compact way. Additionally this allows us to generate relative selections which are typically small, even if they are not the least ones. From now on we will refer to formulas in such logic with "logic formulas".

#definition("logic for upward-closed sets")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Given $n in bb(N)$ we define the following logic, where $b in B_L$ and $i in range(n)$:

  $
    phi := [b, i] | and.big_(k in K) phi_k | or.big_(k in K) phi_k
  $
]

The formulas $tt$ and $ff$ are then implicitly defined as $and_(k in varempty) phi_k$ and $or_(k in varempty) phi_k$.

We now give the semantics of a logic formula, which consist in the set of moves that the formula is representing. We will be interested in formulas whose semantics will be equal to the set $E(b, i)$.

#definition("logic formulas semantics")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula. The semantics of $phi$, that is the set of player 1 vertices is represents, is a upward-closed set $sem(phi) subset.eq (2^(B_L))^n$ with respect to $phsub$, define as follows:
  $
    sem([b, i]) &= { tup(X) | b in tup(X)_i } \
    sem(and.big_(k in K) phi_k) &= sect.big_(k in K) sem(phi_k) \
    sem(or.big_(k in K) phi_k) &= union.big_(k in K) sem(phi_k)
  $
]

Given a logic formula we can however define a generator for symbolic moves, which is a selection for the set represented by the logic formula semantics. This will be the set of moves that we will use in practice when solving the parity game.

// TODO: Composition of moves, system of equations, etc etc?
#definition("generator for symbolic moves")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula. The moves generated by $phi$, written $M(phi)$ are:

  $
    M([b, i]) &= { tup(X) } "with" X_i = { b } "and" forall j != i. X_j = varempty \
    M\(and.big_(k in K) phi_k\) &= { union.big X | X in product_(k in K) M(phi_k) } \
    M\(or.big_(k in K) phi_k\) &= union.big_(k in K) M(phi_k)
  $
]

Another advantage of representing selections using such formulas is that they can be simplified when it becomes known that some position $[b, i]$ for player 0 is winning or losing. This corresponds to the assigning either true or false to the atom $[b, i]$ in the formula and propagating that through the operators it is contained in. In the parity game this would translate to either removing some moves for player 0, due to them being winning for player 1, or replacing ,moves for player 0 moves with a smaller number of them that do not give player 1 the option to reach positions that are winning for player 0. This is already exploited in the existing implementation of the symbolic algorithm @flori to potentially remove lot of edges at once, thus simplifying the game, while preserving the winners on all positions.

// Seen from another point of view, a logic formula $phi$ for $E(b, i)$ represents whether $b$ will be below the solution for $x_i$, expressed as a boolean expression in function of whether some elements of the basis will be below the solutions for some variables, represented by the atoms $[b, i]$. Then $E(b, i)$ represents all the possibly partial assignments that make the formula true, while $M(phi)$ represents only a subset of possibly partial assignments such that no valid assignment exist that is not a superset of those included.

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

We need to define a logic formula representing the moves for player 0 for each vertex $(b, i)$ for a basis element $b$ and a variable index $i$. Recall that the system of equations is defined over $2^bb(S)$, the powerset lattice of its states, while the basis is $B_(2^bb(S))$, consisting of singletons, given in @powerset-basis. We thus need to define a formula for each state $s$ and index $i$ such that the formula is true when the state $s$ satisfies the formula $phi_i (tup(x^*))$, with $tup(x^*)$ representing the actual solution of the system. Moreover we are allowed to refer to any vertex controlled by player 0 in this formula, which is equivalent to being able to require that any another state $s'$ satisfies one of the formulas $phi_j (tup(x^*))$.

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
It is interesting to note that the cases for $diam(A) psi$ and $boxx(A) psi$ are effectively taking the respective semantics definition, which use universal and existential quantifiers, and translating them to finite sequence of respectively conjunctions and disjunctions between the elements that satisfy such quantifiers.

The definition also did not include fixpoint formulas since those were already been removed when translating to a system of fixpoint equations.

// TODO: Example of logic formulas for mucalculus?

=== Translating bisimilarity <bisimilarity-translation>

Likewise for bisimilarity we have seen in @bisimilarity-application that it can be translated to a fixpoint equation, which in turn can be seen as a system of a single fixpoint equation. As with $mu$-calculus formulas the domain is the powerset lattice $2^(bb(S) times bb(S))$, and thus its basis is $B_(2^(bb(S) times bb(S)))$, which can also be expressed as ${ {(s_1, s_2)} | s_1, s_2 in bb(S) }$. Since there is just one variable and equation we will only define $F(s_1, s_2)$, representing the formula for the player 0 vertex $((s_1, s_2), 1)$:

$
  F(s_1, s_2) =
    (
      (and.big_(a in Act) and.big_(s_1 ->^a t_1) or.big_(s_2 ->^a t_2) [(t_1, t_2), 1])
      and
      (and.big_(a in Act) and.big_(s_2 ->^a t_2) or.big_(s_1 ->^a t_1) [(t_1, t_2), 1])
    )
$

#example("logic formulas for bisimilarity")[
  For example the formulas for the pair of states in the labelled transition systems shown in @bisimilarity-example are the following:

  #import "@preview/equate:0.2.0": equate
  #equate($
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
  $)
]


=== Translating parity games <parity-translation>

It is known that parity games can also be translated to nested fixpoints @parity_to_fixpoint, which in turn are equivalent to systems of fixpoint equations. We will later use this fact to generate simple problems for testing our implementation.

In particular, given a parity game $G = (V_0, V_1, E, p)$ we can define a system of fixpoint equations on the boolean lattice $bb(B)$, where $tt$ represents a vertex being winning for player 0 while $ff$ is winning for player 1. Then for each vertex $v in V_0 union V_1$ a variable $x_v$ will be defined along with the following equation:

$
  x_v feq_eta cases(,
    union.sq.big_(u in v E) x_u & "if " v in V_0,
    sect.sq.big_(u in v E) x_u & "if " v in V_1
  )

  #h(4em)
  "with" eta = cases(
    nu & "if" p(v) "even",
    mu & "if" p(v) "odd"
  )
$

Intuitively, a vertex in $V_0$ is winning for player 0 if any of its successors is also winning for them, because they can choose to move to that successor and keep winning. Meanwhile, a vertex in $V_1$ is winning for player 0 if all its successors are winning for them, because otherwise player 1 would have the option to move to any successor that is not winning for player 0 and win.

The priority of vertices must however also be taken into account in order to determine the winner of infinite plays, which we can reduce to plays ending with a cycle. If one happens the last equation corresponding to a vertex of the cycle will have both $tt$ and $ff$ as fixpoint, and will thus decide the winner for the entire cycle, hence why equations corresponding with vertices with higher priorities have to be sorted last. The winner is then chosen by whether the fixpoint equation is a greatest fixpoint or a least fixpoint: if it is a greatest fixpoint the solution will be $tt$ and player 0 will win, otherwise it will be $ff$ and player 1 will win. This is the reason why the fixpoint type was chosen according to the priority of the vertex: if it is even then player 0 wins the cycle in the parity game and hence the equation must be a greatest fixpoint, otherwise player 1 wins and the equation must be a least fixpoint.

These functions can be trivially converted to logic formulas. Notice that the atom $(tt, i)$, where $i$ is the index of the equation with variable $x_u$, is true if and only if the solution for $x_u$ is $tt$, otherwise if the atom is false then the solution is $ff$. As such the equations of the system can be converted to logic formulas by replacing each variable $x_u$ with the atom $(tt, i)$, where $i$ is the index of variable the $x_u$, each $join$ with $or$ and each $meet$ with $and$.

#example("translation and logic formulas for a parity game")[
  For example the parity game in @parity-example would be translated to the following system of fixpoint equations:

  $
    syseq(
      v_0 &feq_nu v_1 join v_2 \
      v_1 &feq_nu v_0 \
      v_2 &feq_mu v_1 meet v_3 \
      v_4 &feq_nu v_2 join v_3 \
      v_3 &feq_mu v_4
    )
  $

  Which can then be translated to the following formulas:

  $
    F(tt, 1) &= [tt, 2] or [tt, 3] \
    F(tt, 2) &= [tt, 1] \
    F(tt, 3) &= [tt, 2] and [tt, 5] \
    F(tt, 4) &= [tt, 3] or [tt, 5] \
    F(tt, 5) &= [tt, 4]
  $
]

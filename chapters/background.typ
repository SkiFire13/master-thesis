#import "../config/common.typ": *

= Background

In this chapter we give an overview of the theoretical background used in the rest of this thesis.
// TODO: Anticipate arguments?

== Lattices

#definition("partial order")[
  Let $X$ a set. A partial order $sub$ is a binary relation on $X$ such that for all $x, y, z in X$ it satisfies the following properties:
  - (Antisymmetry): if $x sub y$ and $y sub x$ then $x = y$;
  - (Reflexivity): $x sub x$;
  - (Transitivity): if $x sub y$ and $y sub z$ then $x sub z$.
]

#definition("poset")[
  Let $X$ be a set and $sub$ a partial order over $X$. A poset is a pair $(X, sub)$.
]

// TODO: Preorder?

#definition("join and meet")[
  Let $(X, sub)$ be a poset and $S subset.eq X$. The meet (respectively join) of $S$, written $meet S$ (resp. $join S$), is the smallest (resp. greatest) element of $X$ that is bigger (resp. smaller) or equal to every element in $S$. Formally:
  - (Meet): $forall s in S. s sub meet S$ and $forall t in X. forall s in S. s sub t => meet S sub t$
  - (Join): $forall s in S. join S sub s$ and $forall t in X. forall s in S. t sub s => t sub join S$
]

Meet and join don't always exist, but when they do it can be proven that they are unique. We will however work with posets where they always exist for our purposes.

#definition("lattice")[
  Let $(L, sub)$ be a poset. It is also a lattice if meet and join exist for every pair of elements, that is given $x, y in L$ both $meet {x, y}$ and $join {x, y}$ are defined.
]

#definition("complete lattice")[
  Let $(L, sub)$ be a lattice. It is also a complete lattice if meet and join exist for every subset, that is given $S subset.eq L$ both $meet S$ and $join S$ are defined.
]

#lemma("finite complete lattices")[
  Let $(L, sub)$ be a finite lattice, that is a lattice where $L$ is a finite set. Then it is also a complete lattice.
]

From now on we will mostly work with finite, and thus complete, lattices.

// TODO: Image example of complete lattice?

#definition("powerset")[
  Let $X$ be a set. Its powerset, written $2^X$, is the set of all subsets of $X$, that is $2^X = {S | S subset.eq X}$.
]

#example("powerset lattice")[
  Given a set $X$, the pair $(2^X, subset.eq)$ is a complete lattice.
]

// TODO: Image example of powerset lattice

#definition("basis")[
  Let $(L, sub)$ be a lattice. A basis is a subset $B_L subset.eq L$ such that all elements of $L$ can be defined by joining subsets of the basis, that is $forall l in L. l = join { b in B_L | b sub l }$.
]

// TODO: Image example of basis of non-powerset

#example("basis of powerset")[
  Given a set $X$, a basis of the poset $(2^X, subset.eq)$ is the set of singletons $B_(2^X) = { {x} | x in X }$.
]

// TODO: upward-closure?

#definition("monotone function")[
  Let $(X, sub)$ be a poset and $f: X -> X$ a function. $f$ is monotone if $forall x, y in X. x sub y => f(x) sub f(y)$
]

#definition("fixpoint")[
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a monotone function. Any element $x in X$ such that $f(x) = x$ is a fixpoint of $f$. \
  The least fixpoint of $f$, written $lfp f$, is the smallest of such elements, while the greatest fixpoint of $f$, written $gfp f$, is the biggest. \
  Thanks to the Knaster-Tarski theorem the existance and uniqueness of the least and greatest fixpoints is guaranteed.
]

// TODO: Mention Kleene iteration and say it is not always feasible (can take omega steps)

// TODO: Image example of fixpoint?

== Tuples

In order to define systems of fixpoint equations we'll need to refer to multiple equations/variables/values together, and to do that we'll use tuples. We introduce here some notations to better distinguish tuples from other values.

#definition("set of tuples")[
  Let $A$ be a set. The set of $n$-tuples of $A$ is $A^n$.
]

#notation("tuple")[
  Let $A^n$ be a set of $n$-tuples. We will refer to its elements using boldface lowercase letters, like $tup(a)$.
]

#notation("tuple indexing")[
  Let $tup(a) in A^n$ be an $n$-tuple. We will refer to its $i$-th element with the non-boldface $a_i$. 
]

#notation("range")[
  We will refer to the set ${ 1, ..., n }$ with the shorthand $range(n)$.
]

#notation("concatenation")[
  Let $tup(a_1), ..., tup(a_k)$ be either tuples or single elements of $A$. The notation $(tup(a_1), ..., tup(a_k))$ represents a tuple made by concatenating the elements in the tuples $tup(a_1), ..., tup(a_k)$. Single elements are considered as $1$-tuples for this purpose.
]

Notice that using concatenation the empty tuple can be represented as $()$.

// TODO: tuple range?

// TODO: define pointwise order (if needed)

== Systems of fixpoint equations

#definition("system of fixpoint equation")[
  Let $(L, sub)$ be a complete lattice. A system of fixpoint equations $E$ is a system of the following shape:

  $
    syseq(
      x_1 &feq(eta_1) &f_1 &(x_1, ..., x_n) \
      x_2 &feq(eta_2) &f_2 &(x_1, ..., x_n) \
          &#h(0.3em)dots.v \
      x_n &feq(eta_n) &f_n &(x_1, ..., x_n) \
    )
  $

  For all $i in range(n)$, $x_i in L$ and $f_i : L^n -> L$ is a monotone function. $eta_i$ is either $mu$ or $nu$, representing either a least or a greatest fixpoint equation.
]

#notation("system of fixpoint equations as tuple")[
  The above system of fixpoint equations can be written as $tup(x) feq(tup(eta)) tup(f)(tup(x))$, where:
  - $tup(x) = (x_1, ..., x_n)$;
  - $tup(f) = (f_1, ..., f_n)$ but also seen as $tup(f): L^n -> L^n$ with $tup(f)(x_1, ..., x_n) = (f_1(x_1), ..., f_n (x_n))$;
  - $tup(eta) = (eta_1, ..., eta_n)$.
]

// TODO: tup(f) monotone according to pointwise order? Is it useful?

#notation("empty system of fixpoint equations")[
  A system of equations with no equations or variables is conveniently written as $emptyset$.
]

In order to describe the meaning of such system of fixpoint equations we'll need a few more notions. We will mostly assume that given a system all the variables will be named $x_i$ for $i in range(n)$.

#definition("substitution")[
  Let $(L, sub)$ be a complete lattice and $E$ be a system of $n$ fixpoint equations over $L$ and variables $x_i$ for $i in range(n)$. Let $j in range(n)$ and $l in L$. The substitution $E[x_j := l]$ is a new system of equation where the $j$-th equation is removed and any use of the variable $x_j$ is replaced with the element $l$.
]

#definition("solution")[
  Let $(L, sub)$ be a complete lattice and $E$ be a system of $n$ fixpoint equations over $L$ and variables $x_i$ for $i in range(n)$. The solution of $E$ is $s = sol(E)$, with $s in L^n$ inductively defined as:

  $
    sol(emptyset) &= () \
    sol(E) &= (sol(E[x_n := s_n]), s_n)
  $

  where $s_n = eta_n (lambda x. f_n (sol(E[x_n := x]), x))$.
]

#example("solving a fixpoint system")[
  Consider the following system of fixpoint equations $E$ on some powerset $2^X$:
  $
    syseq(
      x_1 &feq(mu) x_1 union x_2 \
      x_2 &feq(nu) x_1 sect x_2 \ 
    )
  $
  Solving this system of equations will require the following steps:
  - $sol(E) = (sol(E[x_2 := s_2]), s_2)$ with $s_2 = nu(lambda x. sol(E[x_2 := x]) sect x)$
  - $sol(E[x_2 := x]) = (sol(emptyset), s_1)$ with $s_1 = mu(lambda x'. x' union x)$
  - solving $s_1$ gives $s_1 = x$
  - solving $s_2$ gives $s_2 = nu(lambda x. x sect x) = X$
  - $sol(E) = (X, X)$
]

Notice that the way the solution of a system of fixpoint equations is defined depends on the order of the equations. Indeed different orders can result in different solutions.

#example("different order of equations")[
  Consider $E'$ the same system of fixpoint equations as before, but with the equations swapped:
  $
    syseq(
      x_1 &feq(nu) x_1 sect x_2 \
      x_2 &feq(mu) x_1 union x_2 \
    )
  $
  Solving this system of equations will require the following steps:
  - $sol(E') = (sol(E'[x_2 := s_2]), s_2)$ with $s_2 = mu(lambda x. sol(E'[x_2 := x]) union x)$
  - $sol(E'[x_2 := x]) = (sol(emptyset), s_1)$ with $s_1 = nu(lambda x'. x' sect x)$
  - solving $s_1$ gives $s_1 = x$
  - solving $s_2$ gives $s_2 = mu(lambda x. x sect x) = emptyset$
  - $sol(E') = (emptyset, emptyset)$

  Notice that $sol(E) = (X, X) != (emptyset, emptyset) = sol(E')$
]

== $mu$-calculus
// TODO: Examples with mu-calculus

== Parity games
// TODO: Equivalence with parity game

#definition("parity graph")[
  Let $V$ be a finite set of vertixes partitioneds into $V_0$ and $V_1$, that is $V = V_0 disjunion V_1$, and $p: V -> bb(N)$ be a function. A parity graph is a graph $G = (V_0, V_1, E, p)$, where $E subset.eq V times V$ is a set of edges. $p$ is also called the *priority function* or coloring of the graph.
]

Sometimes a parity graph is also defined as a biparite graph by requiring $E subset.eq V_0 times V_1 union V_1 times V_0$. This will be the case in this thesis and can help practical implementations, but is not required in general.

The codomain of $p$ is traditionally taken to be $bb(N)$, but it can be shown to be equivalent to any finite totally ordered set $P$ partitioned into $P_0$ and $P_1$, respectively corresponding to the set of even and odd priorities.

#definition("parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. A parity game is a game on this graph played by two players, called 0 and 1. The game starts from an initial vertex $v_0$ moves along the edges of the graph, such that if the current vertex is in $V_0$ (resp. $V_1$) then the next move is chosen by player 0 (resp. player 1).
  
  The game continues either infinitely or until a player has no moves available. This gives rise to a potentially infinite sequence of vertices $v_0 v_1 v_2...$ called a *play*, where for each pair $(v_i, v_(i+1)) in E$.

  The winner is decided by the play:
  - if the play is infinite then the highest priority according to $p$ of the infinitely occurring vertexes in the play is considered: is if's even player 0 wins, otherwise player 1 wins;
  - if the play is finite then the last vertex $v_n$ is considered, if $v_n in V_0$ then player 0 wins, otherwise player 1 wins.
]

Players are also sometimes called $lozenge$ and $square$ or $exists$ and $forall$ due to their meaning when using parity games for solving $mu$-calculus or fixpoints.

Sometimes parity graphs are required to contain at least a successor for every node, leading to a parity game where every play is infinite. We'll see later how we can modify an existing parity game to satisfy this constraint without affecting the outcome.
// TODO: Later need to show this.

// TODO: Image example of parity game?

#definition("strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. A strategy for player $i$ is a function $sigma: V_i -> V_(1-i)$ such that $forall v in V_i. (v, sigma(v)) in E$.
]

#definition("winning strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. A winning strategy for player $i$ starting from $v$ is strategy such that the resulting play will be winning for player $i$ no matter which move player $1-i$ will choose.
]

A winning strategy is memoryless, that is it doesn't need to know which moves were performed earlier in the play. This is reflected in the fact that the strategy is a function of the current vertex only.

#lemma("determinacy of parity games")[
  Every parity game $G = (V_0, V_1, E, p)$ is deterministic. The set of vertexes $V$ can be partitioned in two *winning sets* $W_0$ and $W_1$ of the vertexes where player 0 (resp. player 1) has a winning strategy starting from vertexes in that set.
]

== Symbolic formulation and selections

#definition("powerset game")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Let $E = tup(x) feq(tup(eta)) tup(f) (tup(x))$ be a system of $n$ fixpoint equations.

  The powerset game is a parity game associated with $E$ defined as:

  - the vertexes for player 0 are $V_0 = B_L times range(n) = { (b, i) | b in B_L and i in range(n) }$
  
  - the vertexes for player 1 are $V_1 = (2^(B_L))^n = { (X_1, ..., X_n) | X_i in 2^(B_L) }$

  - the edges from player 0 vertexes are $E(b, i) = { tup(X) | tup(X) in (2^(B_L))^n and b sub f_i (join tup(X)) }$

  - the edges from player 1 vertexes are $A(tup(X)) = { (b, i) | i in range(n) and b in X_i }$

  - the priority function is defined such that:
    
    - $p(tup(X)) = 0$;

    - $p((b, i))$ is even if $eta_i = nu$ and odd if $eta_i = mu$;

    - $p((b, i)) < p((b', j))$ if $i < j$.
]

The given priority function is not fully specified, but it can be shown that there exist a mapping to $bb(N)$ that satisfies the given order and partition into even/odd. An intuitive way would be to just list the priorities in order and give to map each of them to the next available even or odd natural number.

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

In practice it's not feasible to consider all the possible edges for player 0. We can however observe that many of them are useless. For every $X$ and $Y$ such that $join X sub join Y$ we'll have $b sub f_i(join X) sub f_i (sub Y)$. This in turn will give player 1 strictly more moves, which intuitively is never better for player 0. Thus all those moves can be excluded. In practice considering the minimal set of moves for player 0 is not feasible, but we can reasonably approximate it in a compact way using symbolic moves.

// TODO: ref to symbolic moves paper

#definition("logic for symbolic moves")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Given $n in bb(N)$ we can define the following logic, where $b in B_L$ and $i in range(n)$:

  $
    phi := [b, i] | and.big_(k in K) phi_k | or.big_(k in K) phi_k
  $
]

#definition("generator for symbolic moves")[
  Let $(L, sub)$ be a complete lattice, $B_L$ a basis of $L$, $n in bb(N)$, $i in range(n)$ and $phi$ a logic formula for symbolic moves. We can define the following generator of reduced moves for player 0:

  $
    M([b, i]) &= { tup(X) } "with" X_i = { b } "and" forall j != i. X_j = emptyset \
    // TODO: Is join correct here?
    M\(and.big_(k in K) phi_k\) &= union.big { join tup(X) | tup(X) in product_(k in K) M(phi_k) } \
    M\(or.big_(k in K) phi_k\) &= union.big { M(phi_k) | k in K }
  $
]

// TODO: Comment, example?

== Local strategy iteration
// TODO: Local strategy iteration

// TODO: (For chapter after background) integrating formulas with local strategy iteration

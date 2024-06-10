#import "../config/common.typ": *

= Background

In this chapter we give an overview of the theoretical background used in the rest of this thesis.

We will first define orders, lattices and monotone functions, which will be the fundamentals for properly defining systems of fixpoint equations, which is what we are actually interested in. We will then give a brief introduction on parity games and how they can be used to characterize the solutions of a system of fixpoint equations, followed by the theory behind two algorithms used to solve them.

== Partial orders, lattices and monotone functions

TODO: Why we need lattices and orders?

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

Meet and join do not always exist, but when they do it can be proven that they are unique. We will however work with posets where they always exist for our purposes.

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

In order to define systems of fixpoint equations we will need to refer to multiple equations/variables/values together, and to do that we will use $n$-tuples.

#definition([set of $n$-tuples])[
  Let $A$ be a set. The set of $n$-tuples of $A$ is $A^n$.
]

It will be helpful to distinguish $n$-tuples from other kind of values and coincisely express common operations on them. We will also often refer to the set of indexes of their element. To do this we will define some convenient notations for them:

#notation([$n$-tuple])[
  Let $A^n$ be a set of $n$-tuples. We will refer to its elements using boldface lowercase letters, like $tup(a)$. Given $tup(a) in A^n$ we will refer to its $i$-th element with the non-boldface $a_i$.
]

#notation("concatenation")[
  Let $tup(a_1), ..., tup(a_k)$ be either $n$-tuples or single elements of $A$. The notation $(tup(a_1), ..., tup(a_k))$ represents a $n$-tuple made by concatenating the elements in the tuples $tup(a_1), ..., tup(a_k)$. Single elements are considered as $1$-tuples for this purpose.
]

Notice that using concatenation the empty tuple can be represented as $()$.

#notation("range")[
  We will refer to the set ${ 1, ..., n }$ with the shorthand $range(n)$.
]

// TODO: tuple range?

// TODO: define pointwise order (if needed)

== Systems of fixpoint equations

#definition("system of fixpoint equation")[
  Let $(L, sub)$ be a complete lattice. A system of fixpoint equations $E$ is a system of the following shape:

  $
    syseq(
      x_1 &feq_eta_1 &f_1 &(x_1, ..., x_n) \
      x_2 &feq_eta_2 &f_2 &(x_1, ..., x_n) \
          &#h(0.3em)dots.v \
      x_n &feq_eta_n &f_n &(x_1, ..., x_n) \
    )
  $

  For all $i in range(n)$, $x_i in L$ and $f_i : L^n -> L$ is a monotone function. $eta_i$ is either $mu$ or $nu$, representing either a least or a greatest fixpoint equation.
]

#notation("system of fixpoint equations as tuple")[
  The above system of fixpoint equations can be written as $tup(x) feq_tup(eta) tup(f)(tup(x))$, where:
  - $tup(x) = (x_1, ..., x_n)$;
  - $tup(f) = (f_1, ..., f_n)$ but also seen as $tup(f): L^n -> L^n$ with $tup(f)(x_1, ..., x_n) = (f_1(x_1), ..., f_n (x_n))$;
  - $tup(eta) = (eta_1, ..., eta_n)$.
]

// TODO: tup(f) monotone according to pointwise order? Is it useful?

#notation("empty system of fixpoint equations")[
  A system of equations with no equations or variables is conveniently written as $emptyset$.
]

In order to describe the meaning of such system of fixpoint equations we will need a few more notions. We will mostly assume that given a system all the variables will be named $x_i$ for $i in range(n)$.

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
      x_1 &feq_mu x_1 union x_2 \
      x_2 &feq_nu x_1 sect x_2 \ 
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
      x_1 &feq_nu x_1 sect x_2 \
      x_2 &feq_mu x_1 union x_2 \
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

== Applications

- TODO: $mu$-calculus
- TODO: bisimilarity
- TODO: parity games as fixpoint on boolean lattice
- TODO: other (take from notes)

== Parity games

TODO: Informal description of parity games
// TODO: Image example of parity game?

// TODO: integrate in the informal description
Players are also sometimes called $lozenge$ and $square$ or $exists$ and $forall$ due to their meaning when using parity games for solving $mu$-calculus or fixpoints.

// TODO: integrate in the informal description
$p$ is usually also called the *priority function* or coloring of the graph. Its codomain is traditionally taken to be $bb(N)$, but it can be shown to be equivalent to any totally ordered set $P$ partitioned into $P_0$ and $P_1$, respectively corresponding to the set of even and odd priorities.

Since we will often use the set of predecessors and successors of a vertex we will define a convenient notation for them. We will also need a formal concept for infinitely recurring elements in a sequence in order to describe the winner of a parity game.

#notation("successors and predecessors")[
  Let $G = (V, E)$ be a graph.
  Given $u, v in V$ we write $u E v$ if the graph contains the edge from $u$ to $v$.
  We write $u E$ as a shorthand for the set ${ v in V | u E v }$ and $E v$ as a shorthand for the set ${ u in V | u E v }$
]

#definition("infinitely recurring elements")[
  Let $pi = v_0 v_1 v_2 ...$ an infinite sequence of elements. We define $inf(pi)$ as the set of infinitely recurring elements of $pi$, that is $inf(pi) = { v | forall n. exists i >= n. v_i = v }$.
]

#definition("parity graph")[
  Let $V$ be a finite set of vertices, $E subset.eq V times V$ a set of edges, and $p: V -> bb(N)$ a so called priority function. A parity graph is a graph $G = (V, E, p)$.
]

// TODO: Concept of "moves" is still too informal.
#definition("parity game, play")[
  Let $(V, E, p)$ be a parity graph and let $V$ be partitioned into two sets $V_0$ and $V_1$. A parity game $G = (V_0, V_1, E, p)$ is a game played between two players 0 and 1 on G, where player $i$ controls the "moves" made from vertices in $V_i$.

  Starting from a vertex $v_0 in V$ we can build a potentially infinite sequence $pi = v_0 v_1 ...$ called a *play*, following the moves performed by the two players. We require that $forall i. v_i E v_(i+1)$, and in case this sequence is finite, that is $pi = v_0 v_1 ... v_n$, we also require $v_n E = emptyset$.

  Given a play we define its *winner*:
  - if it is finite, that is $pi = v_0 v_1 ... v_n$ with $v_n in V_i$ then the winner is player $1-i$;
  - if it is infinite then consider $max inf(p(v_0) p(v_1) ...)$: if it is even the winner is player 0, otherwise it is player 1.
]

We will however focus on parity games that are more restriced than this, in particular we will focus on _bipartite parity games_ and _total parity games_.
Bipartite parity games are parity games whose underlying graph is bipartite, which forces players to perfectly alternate moves.
Total parity games instead require every vertex to have at least one successor, thus forcing every play to be infinite.

We will mostly assume bipartite parity games, while we will show that we can convert any parity game in a compatible total parity game.

#definition("bipartite parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. It is also a bipartite parity game if the graph $(V_0, V_1, E)$ is bipartite, that is $forall v in V_i. v E sect V_i = emptyset$.
]

#definition("total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. It is also a total parity game if every vertex has at least one successor, that if $forall v in V_0 union V_1. v E != emptyset$.
]

=== Strategies

The strategy iteration algorithm heavely depends on the concept of _strategies_, which intuitively represent the way a player can choose its moves in a parity game. We will then see plays as being generated by such strategies, and use this to define what it means to be the winner of a parity game on given vertex.

#definition("strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A strategy for player $i$ is a function taking as input the prefix $v_0 v_1 ... v_n$ of a play such that $v_n in V_i$ and $v_n E != emptyset$ and returns a vertex in $v_n E$.
]

#definition("strategy induced instance")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $sigma$ be a strategy for player 0 and $tau$ be a strategy for player 1. An instance of the game $G$ induced by the strategies $sigma$ and $tau$ is a tuple $(G, sigma, tau)$.

  Given a starting vertex $v_0 in V_0 union V_1$ an instance also uniquely defines a play where if $v_i E != emptyset$ then $v_(i+1) = sigma(v_0 v_1 ... v_i)$ if $v_i in V_0$ and $v_(i+1) = tau(v_0 v_1 ... v_i)$ if $v_i in V_1$, otherwise the play is finite and stops at $v_i$.
  
  // TODO: Do we given a shorthand syntax to such plays?
  It can be proven that if such play is infinite then it will eventually reach a cycle and repeatedly visit those vertexes in the same order, that is the play will be $v_0 ... v_k v_(k+1) ... v_n v_(k+1) ... v_n ...$.
]

#definition("winning strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A strategy $sigma_i$ for player $i$ is called winning on vertex $v$ if for any strategy $sigma_(1-i)$ for the opposing player, the play starting from vertex $v$ in the instance $(G, sigma_0, sigma_1)$ is winning for player $i$.
]

TODO: Cite papers on determinancy (see Jurdzinski)

By the well-known determinancy of parity games we know that each vertex is winning for exactly one of the two players. Moreover it is known that the winning player also has a memoryless winning strategy, that is a strategy that depends only on the current vertex and not on the previous ones. The strategy iteration algorithm will focus on these strategies, as they are much simplier to represent and search for.

#lemma("determinacy of parity games")[
  Given a parity game $G = (V_0, V_1, E, p)$ the winner on each vertex is pre-determined. The set of vertexes $V$ can thus be partitioned in two *winning sets* $W_0$ and $W_1$ of the vertexes where player 0 (resp. player 1) has a winning strategy starting from vertexes in that set.
]

#definition("memoryless strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A memoryless strategy for player $i$ is a strategy that only depends on the last vertex of the play prefix, or equivalently a function that takes as input a vertex $v in V_i$ with $v E != emptyset$ and returns a vertex in $v E$.
]

#lemma("memoryless winning strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and assume that player $i$ has a winning strategy on vertex $v$. Then player $i$ also has a memoryless strategy on the same vertex $v$.
]

== Symbolic formulation and selections

#definition("powerset game")[
  Let $(L, sub)$ be a complete lattice and $B_L$ a basis of $L$. Let $E = tup(x) feq_tup(eta) tup(f) (tup(x))$ be a system of $n$ fixpoint equations.

  The powerset game is a parity game associated with $E$ defined as:

  - the vertexes for player 0 are $V_0 = B_L times range(n) = { (b, i) | b in B_L and i in range(n) }$
  
  - the vertexes for player 1 are $V_1 = (2^(B_L))^n = { (X_1, ..., X_n) | X_i in 2^(B_L) }$

  - the moves from player 0 vertexes are $E(b, i) = { tup(X) | tup(X) in (2^(B_L))^n and b sub f_i (join tup(X)) }$

  - the moves from player 1 vertexes are $A(tup(X)) = { (b, i) | i in range(n) and b in X_i }$

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

== Local strategy iteration

// TODO: Cite paper introducing it.

=== Strategy iteration

Strategy iteration is an algorithm that computes the winning sets and the optimal strategies for the two players of a bipartite and total parity game. The algorithm starts with a strategy for player 0 and repeates _valuation_ phases, during which is computes a _play profile_ for each vertex, and _improvement_ phases, during which it uses such play profiles to improve the strategy. This continues until the strategy can no longer be improved and is guaranteed to be optimal.

// TODO: Something better?
We will now give some general notions that will simplify the following definitions.

#definition("positive and negative vertexes")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. We define $V_+ = { v in V | p(v) "even" }$ and $V_- = { v in V | p(v) "odd" }$.
]

#definition("relevance ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A relevance ordering $<$ is a total order that extends the partial order induced by the $p$ function. In particular $<$ is such that $forall u, v. p(u) < p(v) => u < v$.
]

#definition("reward ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, and let $v, u in V$. We write $u lt.curly v$ when $u$'s reward is less than $v$'s, namely when $u < v$ and $v in V_+$ or $v < u$ and $u in V_-$.
  $
    u lt.curly v <=> (u < v and v in V_+) or (v < u and u in V_-)
  $
]

#definition("reward ordering on sets")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and let $P, Q subset.eq 2^V$ be two different sets of vertexes. Let $v = max_< P Delta Q$. We write $P lt.curly Q$ when $P$'s reward is less than $Q$'s, namely when $v in P$ and $v in V_-$, or when $v in Q$ and $v in V_+$.
  $
    P lt.curly Q <=> P != Q and "max"_< P Delta Q in (P sect V_-) union (Q sect V_+)
  $
]

At the core of the algorithm there is the valuation phase computing the play profiles, which help understand how "good" a play is for each player. In particular an ordering between play profiles is defined, with bigger values being more favourable to player 0 and lower ones being more favourable to player 1. In particular play profiles are based on three key values:

- the most relevant vertex of the cycle (recall that the game is total and thus every play is infinite), which directly correlates to the winner of the play;
- the vertices visited before the most relevant one that are more relevant than it;
- the number of vertices visited before the most relevant.

Intuitively the last two values are linked to the chances that changing strategy would change either the most relevant vertex of the cycle or the cycle itself, thus more relevant vertices before or a longer prefix are more beneficial for the losing player.

#definition("play profile and valuation")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and $pi = v_0 v_1 ...$ a play on $G$. Let $w = max_< inf(pi)$ be the most relevant vertex that's visited infinitely often in the play and $alpha = { u in V | exists i in N. v_i = u and forall j < i. v_j != w }$ be the set of vertexes visited before the first occurence of $w$. Let $P = alpha sect { v in V | v > w }$ and $e = |alpha|$. The play profile of the play $pi$ is the tuple $(w, P, e)$.

  Given an instance $(G, sigma, tau)$ a valuation $phi$ is a function that associates to each vertex the play profile $(w, P, e)$ of the play induced by the instance.
]

#definition("play profile ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, and $(u, P, e)$ and $(v, Q, f)$ be two play profiles. Then we have:
  $
    (u, P, e) lt.curly (v, Q, f) <=> cases(
      & u lt.curly v \
      or ( & u = v and P lt.curly Q) \
      or ( & u = v and P = Q and u in V_- and e < f) \
      or ( & u = v and P = Q and u in V_+ and e > f)
    )
  $
]

Finally, a way to decide whether a strategy can be improved or is optimal is provided. This resolves around looking at the play profiles of the successors of each vertex: if one of them is better than the successor chosen by the current strategy then the strategy is not optimal and the better one can be chosen instead. At this point the valuation is no longer correct and must be recomputed, leading a new iteration.

// TODO: Further details redirect to the paper?
// TODO: Change wording to say the paper implemented it with such complexity.
Each iteration has worst-case complexity $O(|V| dot |E|)$, and in the worst case requires $Pi_(v in V_0) "out-deg"(v)$ many improvement steps.

// TODO: does this need to explain progress relation too or can we assume
// it from the fact a valuation is induced by a pair of strategies?

#theorem("optimal strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, $sigma$ and $tau$ be two strategies for respectively player 0 and 1 and $phi$ a valuation function for $(G, sigma, tau)$.
  $sigma$ is optimal against $tau$ if $forall u in V_0. forall v in u E. phi(v) lt.curly.eq phi(sigma(u))$ and $tau$ is optimal against $sigma$ if $forall u in V_1. forall v in u E. phi(tau(u)) lt.curly.eq phi(v)$.
]

=== Local algorithm

The strategy improvement algorithm has the downside of requiring to visit the whole graph. In some cases this may be a problem, as the graph could be very large but only a small portion may need to be visited to solve the game.

// TODO: Example where this matters?

The local strategy iteration algorithm fills this gap by performing strategy iteration on a _subgame_, a parity game performed on a subgraph of the main game, and providing a way to determine whether this is enough to infer the winner in the full game. It may happen that the winner is not immediately decidable, in which case the subgame would have to be _expanded_. To do this we will need to define what a subgame is, how to expand it and what is the condition that decides the winner on a vertex.

#definition("subgame")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $E' subset.eq E sect (U times U)$, then $G' = (V_0 sect U, V_1 sect U, E', p|_U)$, where $p|_U$ is the function $p$ with domain restricted to $U$, is a subgame of $G$.
]

#definition([$U$-induced subgames])[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. The $U$-induced subgame of $G$, written $G|_U$, is the subgame $(U sect V_0, U sect V_1, E sect (U times U), p|_U)$.
]

#definition("partially expanded game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (U_0, U_1, E', p|_U)$ a subgame of $G$. $G'$ is called a partially expanded game if all its vertexes have at least one successor, that is $forall u in U_0 union U_1. u E' != emptyset$.
]

Given a partially expanded game, two optimal strategies and its winning sets, the local algorithm has to decide whether vertices winning for a player in this subgame are also winning in the full game. Recall that a strategy is winning if any strategy of the opponent always induces a losing play for them. However those plays being losing in the subgame don't necessarily mean that all plays in the full game will be losing too, as they might visit vertices not included in the subgame. Intuitively, the losing player might have a way to force a play to reach one of the vertices just outside the subgame, called the _$U$-exterior_ of the subgame, and thus lead to a play that's not possible in the subgame. The set of vertices that can do this is called the _escape set_ of the subgame, and for such vertices no conclusions can be made, otherwise the winner in the subgame is also the winner in the full game.

#definition($U$ + "-exterior")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. The $U$-exterior of $G|_U$, also written $D_G (U)$, is the set of successors of vertexes in $G|_U$ that are not themselves in $G|_U$. That is:
  $
    D_G (U) = union.big_(v in U) v E sect (V without U)
  $
]

#definition("escape set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma = { (u, v) in E | u in dom(sigma) => sigma(u) = v }$ (resp. $E_tau$) be the set of edges restricted to the strategy for player 0 (resp. 1), and let $E_sigma^*$ (resp. $E_tau^*$) be its transitive-reflexive closure. The escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect D_G (U)$ (resp. $E_L^1 (v) = v E_tau^* sect D_G (U)$).
]

#definition("definitive winning set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame and let $phi$ be a valuation for this instance. The definitive winning sets $W_0$ and $W_1$ are defined as:
  $
    W_0 &= { v in U | E_L^0 (v) = varempty and (phi(v))_1 in V_+ } \
    W_1 &= { v in U | E_L^1 (v) = varempty and (phi(v))_1 in V_- }
  $
]

- TODO: Local algorithm: expansion
- TODO: Local algorithm: complexities (?)

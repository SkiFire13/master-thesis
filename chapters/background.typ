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

In order to define systems of fixpoint equations we will need to refer to multiple equations/variables/values together, and to do that we will use tuples. We introduce here some notations to better distinguish tuples from other values.

#definition("set of tuples")[
  Let $A$ be a set. The set of $n$-tuples of $A$ is $A^n$.
]

TODO: Put notations together

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

In this section we will assume bipartite and total graphs.

TODO: Parity games are known to have winning strategy that doesn't depend on past visited vertices.

#definition("strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A strategy for player $i$ is a function $sigma: V_i -> V_(1-i)$ such that $forall v in V_i. (v, sigma(v)) in E$.
]

// TODO: Better name?
#definition("strategy induced instance")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $sigma: V_0 -> V_1$ be a strategy for player 0 and $tau : V_1 -> V_0$ be a strategy for player 1. An instance of the game $G$ induced by the strategies $sigma$ and $tau$ is a tuple $(G, sigma, tau)$.

  Given a starting vertex $v in V_0 union V_1$ an instance also uniquely defines a play where $v_(i+1) = sigma(v_i)$ if $v_i in V_0$ and $v_(i+1) = tau(v_i)$ if $v_i in V_1$.
]

// TODO: Play consistent with (partial) strategy?

#definition("winning strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. A strategy $sigma_i$ for player $i$ is called winning on vertex $v$ if for any strategy $sigma_(1-i)$ for the opposing player, the play starting from vertex $v$ in the instance $(G, sigma_0, sigma_1)$ is winning for player $i$.
]

A winning strategy is memoryless, that is it does not need to know which moves were performed earlier in the play. This is reflected in the fact that the strategy is a function of the current vertex only.

#lemma("determinacy of parity games")[
  Given a parity game $G = (V_0, V_1, E, p)$ the winner for each starting vertex is pre-determined. The set of vertexes $V$ can thus be partitioned in two *winning sets* $W_0$ and $W_1$ of the vertexes where player 0 (resp. player 1) has a winning strategy starting from vertexes in that set.
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

// Selection
// Selections are equivalent (no proof)
// Symbolic moves
// Symbolic moves are representation of all possible moves
// Symbolic moves are a selection

In practice it is not feasible to consider all the possible edges for player 0. We can however observe that many of them are useless. For every $X$ and $Y$ such that $join X sub join Y$ we will have $b sub f_i(join X) sub f_i (sub Y)$. This in turn will give player 1 strictly more moves, which intuitively is never better for player 0. Thus all those moves can be excluded. In practice considering the minimal set of moves for player 0 is not feasible, but we can reasonably approximate it in a compact way using symbolic moves.

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

// TODO: Cite paper introducing it.
In this section we will assume all parity games to only have infinite plays, in other words for all parity graphs to have no vertex without successors.

=== Strategy iteration

Strategy iteration is an algorithm that computes the winning sets and the optimal strategies for the two players of a parity game. It is based on the notion of _play profiles_, which describe how "good" a play induced by a strategy is.

#definition("positive and negative vertexes")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. We define $V_+ = { v in V | p(v) "even" }$ and $V_- = { v in V | p(v) "odd" }$.
]

#definition("relevance ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph. A relevance ordering $<$ is a total order that extends the partial order induced by the $p$ function. In particular $<$ is such that $forall u, v. p(u) < p(v) => u < v$.
]

#definition("reward ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph with a relevance ordering $<$, and let $v, u in V$. We write $u lt.curly v$ when $u$'s reward is less than $v$'s, namely when $u < v$ and $v in V_+$ or $v < u$ and $u in V_-$.
  $
    u lt.curly v <=> (u < v and v in V_+) or (v < u and u in V_-)
  $
]

The intuition behind the reward ordering is that is represents how "good" a vertex is for each player.

#definition("reward ordering on sets")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph with a relevance ordering $<$ and let $P, Q subset.eq 2^V$ be two different sets of vertexes.

  Let $v = max_< P Delta Q$. We write $P lt.curly Q$ when $P$'s reward is less than $Q$'s, namely when $v in P$ and $v in V_-$, or when $v in Q$ and $v in V_+$.
  $
    P lt.curly Q <=> P != Q and "max"_< P Delta Q in (P sect V_-) union (Q sect V_+)
  $
]

#definition("valuation and play profile")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph with a relevance ordering $<$.
  A valuation $phi$ is a function that associates to each vertex a play profile. We are interested in valuations induced by a pair of strategies for the two players.

  Let $u in V$ and consider the play $pi$ starting from $u$ and induced by the two strategies.
  Let $w$ be the most relevant vertex of $pi$ that is visited infinitely often and let $alpha$ be the set of vertexes visited in $pi$ before the first occurrence of $w$.
  The play profile $phi(u)$ for $u$ is a tuple of:
  - the vertex $w$;
  - the subset of $alpha$ of vertexes more relevant than $w$: $alpha sect {v in V | v > w}$;
  - the size of $alpha$: $|alpha|$.
]

Valuations and play profiles help understand how "good" the strategies are for the two players. This is then described by an ordering on them:

#definition("play profile ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph with a relevance ordering $<$, and $(u, P, e)$ and $(v, Q, f)$ be two play profiles. Then we have:
  $
    (u, P, e) lt.curly (v, Q, f) <=> cases(
      & u lt.curly v \
      or & (u = v and P lt.curly Q) \
      or & (u = v and P = Q and u in V_- and e < f) \
      or & (u = v and P = Q and u in V_+ and e > f)
    )
  $
]

Intuitively, play profiles extend the notion of which player is winning (represented by the first element of the play profile) with informations about how many chances a player has to improve its situation. The ordering between play profiles captures the notion of "how many chances" a player has to do so.

// TODO: does this need to explain progress relation too or can we assume
// it from the fact a valuation is induced by a pair of strategies?

#definition("optimal strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph with a relevance ordering $<$, and $sigma$ and $tau$ be two strategies for respectively player 0 and 1.
  We say that $sigma$ is optimal against $tau$ if $forall u in V_0. forall v in u E. phi(v) lt.curly.eq phi(sigma(u))$ and we say that $tau$ is optimal against $sigma$ if $forall u in V_1. forall v in u E. phi(tau(u)) lt.curly.eq phi(v)$.
]

This allows us to idenfity when a strategy is optimal or can be improved. When the two strategies are both optimal the game is then solved.

In practice the strategy improvement algorithm will alternate a _valuation_ phase, where given a strategy for player 0 an optimal strategy for player 1 is created and a valuation for both is computed, with a _improvement_ phase, where the strategy for player 0 is improved according to the optimality condition. The algorithm repeates the two phases until the optimality condition is true.

// TODO: Further details redirect to the paper?

Each iteration has worst-case complexity $O(|V| dot |E|)$, and in the worst case requires $Pi_(v in V_0) "out-deg"(v)$ many improvement steps.

=== Local algorithm

The strategy improvement algorithm has the downside of requiring to visit the whole graph. In some cases this may be a problem, as the graph could be very large but only a small portion may need to be visited to solve the game.

// TODO: Example where this matters?

The local strategy iteration algorithm fills this gap, by providing a way to perform strategy iteration on an expanding subgame until it has enough informations to decide the winner. To do this we will need to define what a subgame and a partially expanded game is, how to expand it and what is the condition that decides the winner of a vertex.

#definition("induced subgames")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph and $U subset.eq V$. The $U$-induced subgame of $G$, written $G|_U$, is the parity game $(U sect V_0, U sect V_1, E sect (U times U), p|_U)$, where $p|_U$ is the function $p$ with domain restricted to $U$.
]

#definition("partially expanded game")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph and $U subset.eq V$. The $U$-induced subgame $G|_U$ is called a partially expanded game if all its vertexes have at least one successor.
]

#definition($U$ + "-exterior")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph and $U subset.eq V$. The $U$-exterior of $G|_U$, also written $D_G (U)$, is the set of successors of vertexes in $G|_U$ that are not themselves in $G|_U$. That is:
  $
    D_G (U) = union.big_(v in U) v E sect (V without U)
  $
]

#definition("escape set")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph and $U subset.eq V$. Let $sigma$ be an optimal strategy for player 0 on $G|_U$ and $tau$ one for player 1.
  Let $E_sigma = { (u, v) in E | u in dom(sigma) => sigma(u) = v }$ (resp. $E_tau$) be the set of edges restricted to the strategy for player 0 (resp. 1), and let $E_sigma^*$ (resp. $E_tau^*$) be its transitive-reflexive closure. The escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect D_G (U)$ (resp. $E_L^1 (v) = v E_tau^* sect D_G (U)$).
]
// TODO: the L here refers to the "instance" (G|_U, sigma, tau) that has
// not been introduced

Intuitively the escape set represents the vertexes in the $U$-exterior that are reachable from a vertex $v$ controlled by player $i$ assuming the opposite player follows its optimal strategy.

#definition("definitive winning set")[
  Let $G = (V_0, V_1, E, p)$ be a parity graph and $U subset.eq V$. Let $sigma$ be an optimal strategy for player 0 on $G|_U$ and $tau$ one for player 1, let $phi$ be a valuation for this pair of strategies and let $E_L^0$ and $E_L^1$ be the escape sets for the two players. The definitive winning sets $W_0$ and $W_1$ are defined as:
  $
    W_0 &= { v in U | E_L^0 (v) = varempty and (phi(v))_1 in V_+ } \
    W_1 &= { v in U | E_L^1 (v) = varempty and (phi(v))_1 in V_- }
  $
]

That is, a vertex is definitely winning for a player if it is winning in the current $U$-induced subgame and the opposing player has no way to force a play to reach the $U$-exterior, thus every play starting from that vertex stays in the current subgame and conclusions made there stay valid for the whole game.

- TODO: Local algorithm: expansion
- TODO: Local algorithm: complexities (?)

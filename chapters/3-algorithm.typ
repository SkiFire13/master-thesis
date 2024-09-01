#import "../config/common.typ": *

// TODO: Better section title?
= Symbolic local algorithm

== Adapting the algorithm

Our goal will be to adapt and improve the local strategy iteration algorithm to solve systems of fixpoint equations expressed as parity games using the symbolic formulation.

=== Handling finite plays

The parity game formulation of a system of fixpoint equations admits positions where a player has no available moves, namely it is not a total parity game. However the strategy improvement algorithm requires a total parity game, so we need to convert a generic parity game into a "compatible" total parity game that can be handled by it, for some definition of "compatible.

The way we do this transformation is by extending the parity game, inserting auxiliary vertices that will be used as successors for those vertices that do not have one. We call this the _extended total parity game_, for short _extended game_, since it extends the original parity game to make it total. In particular we will add two vertices $w0$ and $w1$ representing vertices that are both controlled by and winning for respectively player 0 and 1. The vertices $w0$ and $w1$ will in turn also need successors, and these will be respectively $l1$ and $l0$, representing vertices that are controlled by and losing for respectively player 1 and 0. Likewise, the vertices $l0$ and $l1$ will need at least one successor, at that will be respectively $w1$ and $w0$. The vertices $w0$ and $l1$ will thus form a forced cycle, as well as $w1$ and $l0$. This, along with priorities chosen as favorable for the player that should win these cycles, will guarantee that the winner will actually be the expected one. Then, vertices that have no successors in the general game, meaning they are losing for the player controlling them, in the game will have as successor $w0$ or $w1$, that is controlled by and winning for the opposing player.

#definition("extended total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. The extended total parity game of $G$ is the parity game $G' = (V'_0, V'_1, E', p')$ where:
  
  #baseline-list[
    - $V'_0 = V_0 union { w0, l0 }$

    - $V'_1 = V_1 union { w1, l1 }$

    - #box(baseline: 2em, $
    E' = E &union { (v, w_i) | i in {0,1} and v in V_(1-i) and v in S_G } \ &union { (w0, l1), (l1, w0), (w1, l0), (l0, w1) }
    $)

    - #box(baseline: 2em, math.equation(block: true, $p'(v) = cases(
        p(v) & "if" v in V \
        0 & "if" v in { w_0, l_1 } \
        1 & "if" v in { w_1, l_0 }
      )$))
  ]
]

We now want to prove that this new parity game is "compatible" with the original one, for a suitable definition of "compatible". In particular for our purposes we are interested that in the new game the winner for vertices which were already in the old game remains unchanged.

#definition("compatible parity games")[
  Let $G = (V_0, V_1, E, p)$ and $G' = (V'_0, V'_1, E', p')$ be two parity games with $V_i subset.eq V'_i$. Let $W_0$ and $W_1$ be the winning sets for $G$ and $W'_0$ and $W'_1$ the winning sets for $G'$. We say that $G'$ is compatible with $G$ if $W_0 subset.eq W'_0$ and $W_1 subset.eq W'_1$.
]

#definition("extended strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the extended game from $G$. Let $sigma$ a strategy on $G$ for player $i$. We say that $sigma$ induces the following extended strategy $sigma'$ on $G'$:
  $
    sigma'(v) = cases(
      sigma (v) & "if" v in V_i and v in.not S_G \
      W_(1-i) & "if" v in V_i and v in S_G \
      W_(1-i) & "if" v = L_i \
      L_(1-i) & "if" v = W_i
    )
  $
]

It can be observed that strategies on a parity game and their extended counterparts create a bijection. In fact notice that the condition $v in V_i and v in.not S_G$ in the first case of $sigma'$ is equivalent to requiring $v in dom(sigma)$, meaning that restricting $sigma'$ to $dom(sigma)$ will result in $sigma$ itself.

The bijection is not only limited to this. It can be showed that strategies that are related by this bijection will also induce plays with the same winner.

#theorem("plays on extended strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the extended game from $G$. Let $sigma_0$ and $sigma_1$ be two strategies on $G$ and $sigma'_0$ and $sigma'_1$ be the unique corresponding strategies on $G'$. Let $v in V_0 union V_1$ and consider the plays starting from $v_0$ on the instances $I = (G, sigma_0, sigma_1)$ and $I' = (G', sigma'_0, sigma'_1)$. The two plays have the same winner.
]

#proof[
  We will prove that for all $i$ the play induced by $I$ is won by player $i$ if and only if the induced play by $I'$ is also won by player $i$:
  - $=> \)$: We distinguish two cases on the play induced by $I$:
    - the play is infinite: $v_0 v_1 v_2 ... $, then every vertex is in $dom(sigma_i)$ for some $i$ and thus $sigma'_i$ are defined to be equal to $sigma_i$ and will induce the same play, which is won by player $i$;
    - the play is finite: $v_0 v_1 ... v_n$, with $v_n in V_(1-i)$ because the play is won by player $i$. For the same reason as the previous point the two induced plays are the same until $v_n$, which is not in $dom(sigma_(1-i))$ but is in $dom(sigma'_(1-i))$. The play induced by $I'$ is $v_0 v_1 ... v_n w_i l_(1-i) w_i ...$ which is also won by player $i$ because only the vertices $w_i$ and $l_(1-i)$ repeat infinitely often, and they have both priority favorable to player $i$.
  - $arrow.l.double \)$: We distinguish the following cases on the play induced by $I'$:
    - the play never reaches the $w_0, w_1, l_0$ or $l_1$ vertices: $v_0 v_1 v_2 ...$, then only the first case of $sigma'_i$ is ever used and thus every vertex is in $dom(sigma_i)$. Thus $I$ induces the same play, which is won by player $i$;
    - the play reaches $w_i$: $v_0 v_1 ... v_n w_i l_(1-i) w_i ...$, then $v_n$ is not in $dom(sigma_(1-i))$ and $I$ induces the finite play $v_0 v_1 ... v_n$ which is won by player $i$ because $v_n in V_(1-i)$ due to its successor being controlled by player $i$;
    - the play reaches $w_(1-i)$: this is impossible because it would be winning for player $1-i$, which contradicts the hypothesis;
    - the play reaches $l_i$ or $l_(1-i)$ before $w_i$ or $w_(1-i)$: this is impossible because the only edges leading to $l_i$ or $l_(1-i)$ start from $w_(1-i)$ and $w_i$.
  #v(-1.8em)
]

#theorem("compatibility of extended games")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the extended game from $G$. Then $G'$ is compatible with $G$, that is $forall i. W_i subset.eq W'_i$.
]

#proof[
  Let $v in W_i$, then there exist a winning strategy $sigma_i$ for player $i$. We claim that the extended strategy $sigma'_i$ for player $i$ on $G'$ is also winning. In fact consider any strategy $sigma'_(1-i)$ for player $1-i$ on $G'$, then it is the extended strategy of some strategy $sigma_(1-i)$ on $G$. We know that the play starting from $v$ on the instance $(G', sigma'_0, sigma'_1)$ is won by the same player as the play starting from $v$ on the instance $(G, sigma_0, sigma_1)$. Moreover since $sigma_i$ is a winning strategy for player $i$ we know that these plays are won by player $i$, thus $v in W'_i$ and so $W_i subset.eq W'_i$.
]

=== Generalizing subgames with subset of edges

The local strategy improvement algorithm gives a way to consider only a subset of the vertices, but still assumes all edges between such vertices to be known. However this is not necessarily true in the symbolic formulation, as the list of successors of vertices in $V_0$ is computed lazily, and this might include vertices already in the subgame. We thus have to update the local algorithm to handle this case by extending the idea of escape set. Instead of identifying those vertices that can reach the $U$-exterior we will identify those vertices that can reach an "unexplored" edge, that is an edge present in the full game but not in the subgame. We will call the vertices directly connected to such edges _incomplete vertices_. Note that the resulting set will be a superset of the $U$-exterior, since edges that lead outside $U$ cannot be part of the subgame.

#definition("subgame")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $E' subset.eq E sect (U times U)$, then $G' = (V_0 sect U, V_1 sect U, E', p|_U)$ is a subgame of $G$, where $p|_U$ is the function $p$ with domain restricted to $U$. We will write $G' = (G, U, E')$ for brevity.
]

#definition("escape set (updated)")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma^*$ (resp. $E_tau^*$) be the transitive-reflexive closure of $E_sigma$ (resp. $E_tau$) and $I_G = {v | v E != v E'}$ the set of vertices that have unexplored outgoing edges. The (updated) escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect I_G$ (resp. $E_L^1 (v) = v E_tau^* sect I_G$).
]

#theorem("definitive winning set is sound")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame where $sigma$ and $tau$ are optimal strategies. Then $W'_0 subset.eq W_0$ and $W'_1 subset.eq W_1$.
]

#proof[
  Let $v in W'_i$, then there exist a strategy $sigma_i$ on $G'$ the for player $i$ such that for any strategy $sigma_(1-i)$ for player $1-i$ on $G'$ the resulting play is winning for player $i$. Moreover $E_L^(1-i) (v) = varempty$ by definition of $W'_i$, meaning that in the graph restricted to the strategy $sigma_i$, any vertex controlled by player $1-i$ that has unexplored edges is not reachable. This in turn means that on the full game $G$ the strategy $sigma_i$ is still winning, because for any strategy $sigma'_(1-i)$ for player $1-i$ on $G$ the resulting play will still be within the subgame, since no unexplored edge can be reached, and any such play is winning for player $i$, hence $v in W_i$.
]

=== Expansion scheme

In the local strategy iteration the expansion scheme is based on the idea of expanding the subgame by adding new vertices. In our adaptation it will instead add new edges, and vertices will be implicitly added if they are the endpoint of a new edge. This does not however change much of the logic behind it, since the expansion schemes defined in @friedmann_local are all based on picking some unexplored successor, which is equivalent to picking the unexplored edge that leads to it.

More formally, the $epsilon_1$ and $epsilon_2$ functions now take the set of edges in the subgame and output a set of new edges to add to the subgame. The requirements remain similar, in that $epsilon_1$ must return a non-empty set of edges that are not already in the subgame and $epsilon_2$ must return a set of outgoing edges from the given vertex. Moreover if a vertex has no successor then $epsilon_2$ must also be non-empty in order to given that vertex a successor and make the game total.

#definition("expansion scheme (updated)")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. An expansion scheme is a pair of functions $epsilon_1 : 2^E -> 2^E$ and $epsilon_2 : 2^E times V -> 2^E$ such that:

  - $varempty subset.neq epsilon_1 (E') subset.eq E without E'$
  
  - $epsilon_2 (E', v) subset.eq ({v} times v E) without E'$

  - $v E = D_G (U, v) => epsilon_2 (E', v) != varempty$
]

As before the expansion is computed by first applying $epsilon_1$ and then by repeatedly applying $epsilon_2$.

#let expand = text(font: "", smallcaps("Expand"))

$
  expand(E') &= expand_2 (E', epsilon_1 (E')) \ \
  expand_2 (E', E'') &= cases(
    E & "if" E'' = varempty \
    expand_2 (E' union E'', union.big_((u, v) in E'') epsilon_2 (E' union E'', v)) & "otherwise"
  )
$

For our implementation we decided to adapt the symmetric expansion scheme from @friedmann_local. The adapted $epsilon_1$ picks any edge from a vertex in the escape set of $v^*$ for the losing player $i$, that is, $epsilon_1 (E') = { e }$ for $e in (v times v E') without E'$, some $v in E^i_L (v^*)$ and $p((phi(v^*))_1) "mod" 2 equiv 1 - i$, while the adapted $epsilon_2$ picks any unexplored edge from the given vertex $v$ if it has no successors, that is $epsilon_2 (E', v) = { e }$ for some $e in (v times v E') without E'$ if $v E' = varempty$, otherwise $epsilon_2 (E', v) = varempty$. The choices it makes are almost the same as those of the original symmetric algorithm if each chosen edge is replaced with its head vertex, with the exception that it may select edges that lead to already explored vertices.

It should be noted that the upper bound on the number of expansions grows from $O(|V|)$, caused by when each expansions adds only a single vertex to the subgame, to $O(|E|)$, now caused by when each expansion adds only one edge to the subgame. As shown in @friedmann_local, a big number of expansions might not be ideal because each will require at least one strategy iteration, which in the long run can end up being slower than directly running the global algorithm.

On the other hand a lazier expansion scheme can take better advantage of the ability to perform simplifications on symbolic moves, which allows to remove lot of edges with little work. A eager expansion scheme may instead visit all those edges, just to ultimately find out that they were all losing for the same reason. There is thus a tradeoff between expanding too much in a single step, which loses some of the benefits of using symbolic moves, and expanding too little, which instead leads to too many strategy iterations.

=== Symbolic formulas and simplification

Differently from the implementation in @flori, we need to generate symbolic moves lazily in order to take advantage of the local algorithm and the simplification of formulas. To do this we represent the generator for symbolic moves described in @upward-logic as a sequence of moves rather than as a set. Then, we can generate moves in the same order they appear in the sequence, and keep track of which point we have reached.

For sake of simplicity we assume that every $and$ and $or$ operator with a single subformula can be first simplified to that subformula itself, while $and$ and $or$ operators with more than two subformulas can be rewritten to nested $and$ and $or$ operators each with exactly two subformulas using the associative property. We thus define the sequence of moves for each type of formula as follows, where for the recursive case we take $M(phi_i) = (tup(X)_(i 1), tup(X)_(i 2), ..., tup(X)_(i n))$:

$
  M([b, i]) &= (tup(X)) "with" X_i = {b} "and" forall j != i. X_j = varempty \
  M(tt) &= (tup(X)) "with" forall i. X_i = varempty \
  M(ff) &= () \
  M(phi_1 or phi_2) &= (tup(X)_11, tup(X)_12, ..., tup(X)_(1 n) tup(X)_21, tup(X)_22, ..., tup(X)_(2 m)) \
  M(phi_1 and phi_2) &= (tup(X)_11 union tup(X)_21, ..., tup(X)_(1 1) union tup(X)_(2 m), tup(X)_12 union tup(X)_21, ..., tup(X)_(1 n) union tup(X)_(2 m))
$

Intuitively a formula $[b, i]$ represents a sequence consisting of a single element, $tt$ also represents a sequence of a single winning move for player 0, while $ff$ represents an empty sequence which is thus losing for player 0. The $or$ operator represent concatenating the two (or more) sequences, with the left one first, and the $and$ operator is equivalent to the cartesian product of the two (or more) sequences, by fixing an element of the first sequence and joining it with each element of the second sequence, then repeating this for all elements of the first sequence.

// For the operator $and$ in particular it can be helpful to imagine its sequence as listing 2-digits numbers, with the tens digit representing the move from the left subformula and the ones digit representing the move from the right subformula. Intuitively doing this means fixing the left digit first and incrementing the second one 

In practice the implementation is based on _formula iterators_, on which we define three operations:
- getting the current move;
- advancing the iterator to the next move, optionally signaling the end of the moves sequence;
- resetting the iterator, thus making it start again from the first move.

These are implemented for every type of formula:

- for $[b, i]$ formula iterators:
  - the current move is always $tup(X)$ with $X_i = {b}$ and $forall j != i. X_j = varempty$;
  - advancing the iterator always signals that the sequence has ended, since there is ever only one move;
  - resetting the iterator always does nothing, since the first move is always the end represented by the iterator.
- for $phi_1 or phi_2$ formula iterators:
  - the current move is the current move of the currently active subformula iterator, which is kept as part of the iterator state;
  - advancing the iterator means advancing the iterator of the currently active subformula, and if that signals the end of the formula then the next subformula becomes the active one. If there is no next subformula then the end of the sequence is signaled;
  - resetting the iterator means resetting the iterators for both subformulas and making $phi_1$ the currently active subformula.
- for $phi_1 and phi_2$ formula iterators:
  - the current move is always the union of the current move of the two subformula iterators;
  - advancing the iterator means advancing the iterator of the right subformula, and if that reports the end of the sequence then it is resetted and the iterator for the left subformula is advanced. If that also reports the end of its sequence then this iterator also reports the end of its sequence;
  - resetting the iterator means resetting the iterators of both subformulas.

As mentioned briefly in @upward-logic, in LCSFE @flori formulas are simplified once before exploring their moves according to the assumptions on the winner for each vertex made at that point in the exploration. This is however not applicable to our case since we lazily explore moves, and thus have to simplify formulas whose moves have already been partially explored. An option would be performing simplifications anyway, losing the information about which moves have already been explored and thus needing to explore them again. We however want to preserve this information to avoid exploring moves over and over, and thus need a way to simplify formulas while tracking the effects on their iterator.

The way we do this is by considering how the operation of simplifying a formula iterator can be seen on their sequence. It turns out that simplifying a formula is equivalent to removing some elements from its sequence, in particular simplifying a formula to $ff$ removes all the moves from its sequence, while simplifying a formula to $tt$ removes all the moves from its sequence except the first winning one. Simplifying a formula iterator then requires simplifying its subformula iterators, which in turn might remove moves from the parent formula iterator. The current move may also be among those removed moves, in which case the iterator might need to be advanced to the next remaining move, potentially reaching its end.

When simplifying we will be interested, for every subformula, about whether it has been simplified to $tt$, $ff$ or whether its truth value is still unknown. In case it has not been simplified to $ff$ we will also care about whether it has reached the end of its sequence after the simplification, and if not whether the current move has changed or not. This will be useful to update the current move of the parent formula iterators. In particular:

- for $[b, i]$ formulas, simplifying them depends on whether it is known that the position for player 0 corresponding to that atom is definitely winning or not:
  - if it is definitely winning the iterator remains unchanged, since the only move in the sequence it represents is winning, while the information that it is winning is propagated to the parent formula iterator;
  - if it is definitely losing the iterator is replaced with $ff$, effectively removing all moves from the sequence;
  - if it is neither of them then the iterator is not changed.
- $tt$ and $ff$ formulas do not need to be simplified, since they are already as much simplified as possible;
- for $or$ formulas, each subformula is simplified, thus any move that is removed from those subformulas sequences is also removed from the $or$ sequence. Then:
  - if one of the subformulas is simplified to $tt$ then the $or$ iterator becomes equal to that subformula iterator. The current move is updated based on whether the winning move was before the current move, in which case the iterator reaches its end, the current move itself, in which case it remains the same, or after the current move, in which case the current move it updated to the winning move.
  - if all the subformulas are simplified to $ff$ then this formula is also simplified to $ff$ and reaches its end;
  - otherwise the current move is updated to the new current move of the current subformula if it has not reached its end, to the first move of the next subformula if that exists, which becomes the new active subformula, or the iterator signals having reached the end of the sequence.
- for $and$ formulas each subformula is simplified and moves that use removed moves from any subformulas are removed. Then:
  - if any subformula has been simplified to $ff$ then the whole formula also simplified to $ff$ and reaches its end;
  - if all subformulas have been simplified to $tt$ then this formula also simplifies to $tt$. If the current move is the winning one nothing changes, otherwise if the first subformula whose winning move is not the current one had already considered that move the iterator reaches its end, if not the current move is advanced until the winning one;
  - otherwise the first subformula from the left that has reached its end causes the advance of the subformula on its left and the reset of itself and all the ones on its right. If there is no subformula on its left the whole iterator has reached its end.

// If a subformula is simplified to $tt$ then its sequence of moves is replaced with one containing its first winning move, while if a subformula is simplified to $ff$ then its sequence of moves is replaced with an empty one. From the point of view of the parent formula iterator, this is equivalent to removing all the moves that involve one of the moves of that subformula. 

//  If the current move is included in this removed moves then the iterator must advance to the next remaining move, if it exists, or signal that it has reached its end. 

// To do this we need to track some informations about the subformulas iterator when they are simplified, namely:
// - whether those iterators also became $tt$ or $ff$;
// - if they did not became $tt$ or $ff$, which of the following three cases they fall on:
//   - the current move is still the same;
//   - the current move has been removed and a new one has taken its place;
//   - the current move has been removed and the sequence has ended.
// - if they did became $tt$, whether a winning move:
//   - is the current move;
//   - has been considered before the current one;
//   - has yet to be considered.

// The simplification algorithm then works similarly to the existing one for simplifying a formula iterator, but in addition:

// - for $phi_1 or phi_2$ formula iterators:
//   - if the formula has been simplified to $tt$ then consider the first subformula that has been simplified to $tt$:
//     - if it is the subformula before the current subformula, or it is the current subformula but it reports to have already considered a winning move, then this formula has also already considered a winning move;
//     - if it is the current subformula and it reports that the winning move is the current one, then the winning move of the whole formula is also the current one;
//     - otherwise the winning move has yet to be considered.
//   - if the formula has not been simplified to either $tt$ or $ff$, then:
//     - if the current subformula has been simplified to $ff$ or has reached its end then this iterator needs to advance;
//     - otherwise the current move is the same as the current subformula iterator one, which might still be the same or have changed to a new one.
// - for $phi_1 and phi_2$ formula iterators:
//   - if the formula has been simplified to $tt$ then:
//     - if the left subformula has already considered a winning move then this iterator has also already considered a winning move;
//     - if the left subformula current move is winning then this iterator winning move depends on when the right subformula winning move;
//     - if the left subformula has not considered a winning move yet then this iterator has also not considered a winning move yet.
//   - if the formula has not been simplified to either $tt$ or $ff$, then:
//     - if the left subformula has been simplified to $tt$:
//       - if it has already considered a winning move, then this iterator has reached its end;
//       - if its current move is winning then the current move is the same as the right subformula iterator one, which might still be the same or have changed to a new one;
//       - if it has not considered a winning move yet, then reset the right subformula iterator, and the current move has changed;
//     - if the right subformula has been simplified to $tt$:
//       - if it has already considered a winning move then advance the left subformula iterator and the current move has changed;
//       - if its current move is winning then the current move remains the same;
//       - it it has yet to consider a winning move then the current move has changed.
//     - if neither has been simplified to $tt$ then:
//       - if the left subformula iterator has reached its end then the whole formula also has;
//       - if the left subformula current move has changed then reset the right subformula iterator, and the current move of this iterator has also changed;
//       - if the left subformula current move is the same and the right subformula iterator has reached its end then advance the left subformula iterator:
//         - if that reaches its end then this iterator also has reached its end;
//         - otherwise this iterator current move has changed.
//       - if the left subformula current move is the same and the right subformula iterator has not reached its end then 

== Improvements

=== Graph simplification

In the local strategy iteration it may happen that we learn about the winner on a vertex that is not the one we are interested in. When this happens we will do a lot of wasted work in the subsequent valuations steps, since it will have to visit its edges again and again.
We now propose a transformation that produces a compatible graph and reduces the amount of edges of vertices in the definitely winning sets, thus decreasing the amount of work that the valuation step needs to perform. Informally, the idea will be to replace all outgoing edges from vertices in a definitely winning set with one pointing to one of the four auxiliary vertices $w0$, $l0$, $w1$ or $l1$ in such a way that its winner is preserved and the graph remains bipartite.

#definition("simplified graph")[
  Let $G = (V'_0, V'_1, E', p)$ be the extended game of some game $(V_0, V_1, E, p)$, let $G' = (G, U, E'')$ be a partially expanded game with ${w0, l0, w1, l1} in U$ and let $W'_0$ and $W'_1$ be the definitely winning sets of $G'$. Let $v in (V_0 union V_1) sect (W'_0 union W'_1)$, then $G$ can be simplified to the graph $G'' = (V'_0, V'_1, E''', p)$ where:
  
  - if $v in V_0 sect W'_0$ then $E''' = E' without v E'' union {(v, l1)}$;
  - if $v in V_0 sect W'_1$ then $E''' = E' without v E'' union {(v, w1)}$;
  - if $v in V_1 sect W'_1$ then $E''' = E' without v E'' union {(v, l0)}$;
  - if $v in V_1 sect W'_0$ then $E''' = E' without v E'' union {(v, w0)}$;
]

#theorem("simplified graph compatible")[
  Let $G = (V_0, V_1, E, p)$ be an extended parity game which has been simplified to $G'' = (V'_0, V'_1, E', p)$ according to the previous definition. Then $G''$ is compatible with $G$.
]
#proof[
  We want to prove that the winning sets in $G$ are equal to the ones in $G''$, that is $forall i. W_i = W''_i$. Without loss of generality we assume the simplification has happened on a vertex $v in W'_0$.
  Consider now any vertex $u in W_i$, that is winning for some player $i$ in $G$. We want to prove that $u in W''_i$ too. Consider any winning strategy for player $i$ and any other strategy for player $1-i$ in $G$. Any play in $G$ induced by these two strategies will be winning for player $i$ since we have $v in W_i$. We now distinguish two cases:
  - $i = 0$, then these plays could reach vertex $v$. The corresponding play in $G''$ would then also reach $v$, but would then only be able to reach $l1$, $w0$ and loop between them. The resulting play would is however also won by player 0, hence $v in W''_0$.
  - $i = 1$, then it is not possible for the play in $G$ to reach vertex, since otherwise player 0 would have a strategy to continue the play and win it, resulting in $u in W_0$ instead of $W_1$. Hence all plays in $G$ do not go through $v$ and remain the same in $G'$, thus remaining winning for player 1 and $u in W''_1$.
]

=== Computing play profiles of the expansion

Each game expansion is normally followed by a strategy iteration step, which computes the play profile of each vertex and then tries to improve the current strategy. We can notice however that the play profiles of all the vertices are known right before the expansion, and if we keep the current strategies fixed, both for player 0 and 1, then the newer vertices cannot influence the play profiles for the existing vertices, since the existing strategies will force any play to remain within the edges in the old subgame. Hence, we can compute the play profiles for the newer vertices in isolation, and only then determine if the existing strategies can be improved given the newer vertices.

It is known that a play profile on a vertex depends on the vertex itself and on the play profile of its successor according to the strategy for the player controlling that vertex. In particular, given a vertex $x$ and its successor $y$ we know the following about its play profile components $phi_0$, $phi_1$ and $phi_2$:

$
  phi_0 (x) &= phi_0 (y) \
  phi_1 (x) &= cases(
    phi_1 (y) & "if" x < phi_0 (x) \
    varempty & "if" x = phi_0 (x) \
    phi_1 (y) union {x} & "if" x > phi_0 (x)
  ) \
  phi_2 (x) &= cases(
    phi_2 (y) + 1 & "if" x != phi_0 (x) \
    0 & "if" x = phi_0 (x)
  )
$

Notice however how this can result in a cyclic dependency if we need to compute the play profiles of multiple vertices creating a cycle. We thus distinguish two cases:

- if the expansion stops by reaching an existing vertex then its play profile was already known and there is no cyclic dependency. Each play profile can be computed based on the one of the successor, starting with the play profile of the last new vertex found;
- if the expansion stops by reaching a vertex found in the current expansion then there is a cyclic dependency. The cyclic dependency can however be broken by finding the most relevant vertex of the cycle $w$, for which we know that $phi (w) = (w, varempty, 0)$. This then breaks the cyclic dependency, since we know the play profile of one of the vertices in the cycle, and we can compute the play profiles of the rest like in the previous case.

By computing the play profiles after an expansion step we can thus perform an improvement right away without having to go through a valuation step to recompute the play profiles. We can further improve this by noticing that the play profiles of existing vertices did not change, thus allowing us to skip the improvement check for any vertex that did not have an outgoing edge just added.

Ultimately this allows us to skip a lot of valuation steps, which are relatively expensive. This also allows to reduce some of the downsides of the local algorithm, among which there is an increased amount of valuation steps required.

=== Exponentially increasing expansions

While lazier expansion schemes are intuitively better when paired with symbolic moves simplification, and the incremental play profiles computation helps often removes the need to perform an expensive valuation step, it can still happen that games fall into the worst case of expanding only a handful of edges in each iteration without being able to perform significant simplifications. This can be avoided by expanding more eagerly, like in the asymmetric expansion scheme for the local strategy improvement algorithm, but ideally we would like to be lazier when possible.

We thus changed the expansion logic to repeatedly expand until a minimum amount of edges has been added to the game. We choose this number to be initially pretty small in order to favour the locality of the algorithm, but made it increase to favour more eager expansions once it becomes clear that the winner cannot be quickly determined locally.

There are multiple ways to perform this increase, and this will influence the final complexity of the algorithm. In our case we choose to increase this number exponentially, thus guaranteeing that the maximum number of expansions is logarithmic in the amount of edges and keeping the cost of the worst cases under control.

To see why this is the case consider the sum of the number of edges $e_i$ added in each expansion $i$. We require each $e_i$ to be at least $a times b^i$ for some constants $a > 0$ and $b > 1$. This creates a geometric progression, whose sum is known to be $a (b^n - 1) / (b - 1)$, though for our purposes we can focus only on bounding it by $a b ^ n$.

$
  "#edges added"
  &= e_0 + e_1 + e_2 + ... + e_n \
  &>= a + a b + a b ^ 2 + ... + a b ^ n \
  &>= a b ^ n
$

Then we know that in the worst case we can add at most $|E|$, since those are all the edges. This gives the equation $|E| >= a b ^ n$, which if we solve for $n$ given $n <= log_b (|E|) / a$.

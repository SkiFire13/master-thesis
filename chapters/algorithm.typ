#import "../config/common.typ": *

// TODO: Better section title?
= Symbolic local algorithm

== Adapting the algorithm

Our goal will be to adapt and improve the local strategy iteration algorithm to solve systems of fixpoint equations expressed as parity games using the symbolic formulation.

=== Handling finite plays

The parity game formulation of a system of fixpoint equations admits positions where a player has no available moves, meaning it is not a total parity game. However the strategy improvement algorithm requires a total parity game, so we need to convert a generic parity game into a "compatible" total parity game that can be handled by it, for some definition of "compatible.

The way we do this transformation is by providing new vertices as successors for those vertices that don't have one. These successors are two fake vertices $w0$ and $w1$, which can only loop respectively with $l1$ and $l0$, another two new vertices. The priorities are then chosen so that any play ending in such loops will be winning for the same player that would have won the otherwise finite play.

#definition("induced total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. The induced total parity game of $G$ is the parity game $G' = (V'_0, V'_1, E', p')$ where:
  
  #baseline-list[
    - $V'_0 = V_0 union { w0, l0 }$

    - $V'_1 = V_1 union { w1, l1 }$

    - $E' = E union { (v, w_i) | i in {0,1} and v in V_(1-i) and v E = varempty } union { (w0, l1), (l1, w0), (w1, l0), (l0, w1) }$

    - #box(baseline: 2em, math.equation(block: true, $p'(v) = cases(
        p(v) & "if" v in V \
        0 & "if" v in { w_0, l_1 } \
        1 & "if" v in { w_1, l_0 }
      )$))
  ]
]

We now want to prove that this new parity game is "compatible" with the original one. In particular for our purposes we will require the new graph to preserve the winners for the vertices in the old graph.

#definition("compatible parity games")[
  Let $G = (V_0, V_1, E, p)$ and $G' = (V'_0, V'_1, E', p')$ be two parity games. Let $W_0$ and $W_1$ be the winning sets for $G$ and $W'_0$ and $W'_1$ the winning sets for $G'$. We say that $G'$ is compatible with $G$ if $W_0 subset.eq W'_0$ and $W_1 subset.eq W'_1$.
]

#theorem("compatibility of induced total parity games")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. We want to prove that $G'$ is compatible with $G$. We will do this by showing that for any play in either parity game there is an equivalent play in the other game won by the same player.

  // TODO: This is just sketched, need to write more formally and nicely
  // IDEA: play is $v_1 v_2 ... v_k overline(v_(k+1) ... v_n)$ where
  //       $v_(k+1) .. v_n$ repeats infinitely many times.
  //       The tail can be empty, in which case the play is finite.
  //       The conversion between G and G' simply transforms any empty
  //       tails in either $overline(w1 l0)$ or $overline(w0 l1)$.
  - ($G$ to $G'$) we can distinguish two kind of plays:
    - (infinite play $v_1 v_2 ...$) the same play is possible in $G'$;
    - (finite play $v_1 v_2 ... v_n$) take $i$ such that $v_n in V_i$, then the play $v_1 v_2 ... v_n w_(1-i) l_i w_(1-i) ...$ is equivalent to the given play. The set of infinitely repeating vertexes is ${ w_(1-i), l_i }$, both of which have the same parity in favour of the player $1-i$;
  - ($G'$ to $G$) we can distinguish two kind of plays:
    - (infinite play $v_1 ... v_n w_(1-i) l_i w_(1-i) ...$ with $v_n$ in $V_i$) this play is winning for player $1-i$, and so is the finite play $... v_n$;
    - (infinite play $v_1 ... v_n v_(n+1) v_(n+2) ...$) the same play is possible in $G$.
]

=== Lazy successors

The local strategy improvement algorithm assumes that given a subset $U$ of the vertexes all edges with both endpoints in $U$ are immediately known, that is $E sect (U times U)$ is immediately known. Unfortunately this is not true in the symbolic formulation, as the list of successors of a vertex is computed lazily, and that might include vertexes in $U$. In other words, with the symbolic formulation we are considering not only a subset of the vertexes, but also a subset of the edges.

// TODO: Show how the local algorithm changes for this (escape set -> edges?)
// TODO: Prove this is ok
- TODO: Ok Not immediately visiting all edges (complexity?)

\

- TODO: Ok removing edges to unfavorable definitely-winning vertexes
- TODO: How to remove edges lazily in formulas (set atom to T/F)
- TODO: (Maybe) Compute play profiles of expanded nodes
- TODO: (Maybe) Only consider unknown/improving vertexes

// - observations:
//   - expansion for p0 is useful if it improves play profiles
//   - play profiles depends only on transitive successors
//   - existing strategy cannot go out of existing graph
//   - play profiles of existing graph do not depend on expansion
//   - so play profiles of expansion can freely depend on existing graph
//     - that is, no cycles between existing graph and expansion
//   - two cases for how expansion ends:
//     - on vertex in expansion -> compute play profile of cycle
//     - on vertex in existing graph -> compute play profile of chain
//   - computed incrementally and on-the-fly to prune p0 moves
//     - require improving play profile
//     - possibly winning for p0
//   - note: once done the play profiles are no longer optimal
//     - assumption: symmetric expansion and not repeated
//     - unless non-improving expansion, then it can be re-expanded.
// Pratically speaking:
// - when picking the existing p0 vertex from which to expand we can
//   store the valuation of its strategy successor
// - when expanding we should keep track of:
//   - the distance traveled
//   - the nodes seen sorted by priority
// - when generating moves from formulas we can inspect each (b, i) and
//   - they could be unexplored, thus can be kept
//   - they could be explored, thus compute the profile for the initial
//     successor. Ignore this node if the profile is not improving.
//   (TODO: test if this is convenient or too costly)
// Note: when expanding from p1 nodes the most favourable profile
// becomes the "smallest" one.
//
// TODO: maybe do something smart with nodes in the expansion too?
// TODO: this means that subsequent expansions without recomputing
//       profiles will see stale/wrong valuations unless we reached
//       a vertex with no improving successors.

#import "../config/common.typ": *

// TODO: Better section title?
= Symbolic local algorithm

== Adapting the algorithm

Our goal will be to adapt and improve the local strategy iteration algorithm to solve systems of fixpoint equations expressed as parity games using the symbolic formulation.

=== Handling finite plays

The parity game formulation of a system of fixpoint equations admits positions where a player has no available moves, meaning it is not a total parity game. However the strategy improvement algorithm requires a total parity game, so we need to convert a generic parity game into a "compatible" total parity game that can be handled by it, for some definition of "compatible.

The way we do this transformation is by providing auxiliary vertices that will be used as successors for those vertices that do not have one, in particular we will add two vertices $w0$ and $w1$ representing vertices that are both controlled by and winning for respectively player 0 and 1. These will be used for vertices that have no successors, meaning they are losing for the player controlling them and thus need a successor that is controlled by and winning for the opposite player. $w0$ and $w1$ will in turn also need successors, and these will be respectively $l1$ and $l0$, representing vertices that are controlled by and losing for respectively player 1 and 0. The vertices $w0$ and $l1$ will thus form a forced cycle, as well as $w1$ and $l0$. This, along with priorities choosen favourable to the player that should win these cycles, will guarantee that the winner will actually be the expected one.

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

We now want to prove that this new parity game is "compatible" with the original one, for some definition of "compatible". In particular for our purposes we are interested in the new graph preserving the winners for the vertices in the old graph.

#definition("compatible parity games")[
  Let $G = (V_0, V_1, E, p)$ and $G' = (V'_0, V'_1, E', p')$ be two parity games. Let $W_0$ and $W_1$ be the winning sets for $G$ and $W'_0$ and $W'_1$ the winning sets for $G'$. We say that $G'$ is compatible with $G$ if $W_0 subset.eq W'_0$ and $W_1 subset.eq W'_1$.
]

#definition("strategy on induced total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. Let $sigma$ a strategy on $G$ for player $i$. $sigma$ induces the following $sigma'$ strategy on $G'$:
  $
    sigma'(v) = cases(
      sigma(v) & "if" v in V_i and v E != emptyset \
      W_(1-i) & "if" v in V_i and v E = emptyset \
      W_(1-i) & "if" v = L_i \
      L_(1-i) & "if" v = W_i
    )
  $
  // TODO: Should this be a lemma?
  Note that there exist a bijection between strategies on $G$ and $G'$.
]

#theorem("plays on induced strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. Let $sigma_0$ and $sigma_1$ be two strategies on $G$ and $sigma'_0$ and $sigma'_1$ the induced strategies on $G'$. Let $v in V_0 union V_1$ and consider the plays starting from $v$ on the instances $(G, sigma_0, sigma_1)$ and $(G', sigma'_0, sigma'_1)$. The two plays are won by the same player.

  TODO: Proof
]

#theorem("compatibility of induced total parity games")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. We want to prove that $G'$ is compatible with $G$, that is $forall i. W_i subset.eq W'_i$.

  // TODO: Better "Proof" label
  Proof.\
  Let $v in W_i$, then there exist a winning strategy $sigma_i$ for player $i$. We claim that the induced strategy $sigma'_i$ for player $i$ on $G'$ is also winning. In fact consider any strategy $sigma'_(1-i)$ for player $1-i$ on $G'$, then it is induced by a strategy $sigma_(1-i)$ on $G$. We know that the play starting from $v$ on the instance $(G', sigma'_0, sigma'_1)$ is won by the same player as the play starting from $v$ on the instance $(G, sigma_0, sigma_1)$. Moreover since $sigma_i$ is a winning strategy for player $i$ we know that these plays are won by player $i$, thus $v in W'_i$ and so $W_i subset.eq W'_i$.
]

=== Lazy successors

The local strategy improvement algorithm gives a way to consider only a subset of the vertices, but still assumes all edges between such vertices to be known. Unfortunately this is not true in the symbolic formulation, as the list of successors of vertices in $V_0$ is computed lazily, and this might include vertices already in the subgame. We can however update the local algorithm to handle this case by extending the idea of escape set. Instead of identifying those vertices that can reach the $U$-exterior we will instead identify those vertices that can reach an "unexplored" edge, that is an edge present in the full game but not in the subgame. We will call the vertices directly connected to such edges _incomplete vertices_. Note that the resulting set will be a superset of the $U$-exterior, since edges that lead outside $U$ cannot be part of the subgame.

#definition("incomplete vertex")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. The set of incomplete vertices is $I_G(E') = { v | v E != v E' }$.
]

#definition("escape set (updated)")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma^*$ (resp. $E_tau^*$) be the transitive-reflexive closure of $E_sigma$ (resp. $E_tau$). The updated escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect I_G (E')$ (resp. $E_L^1 (v) = v E_tau^* sect I_G (E')$).
]

#theorem("definitive winning set sound")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. Let $L = (G|_U, sigma, tau)$ be an optimal instance of the subgame. Then $W'_0 subset.eq W_0$ and $W'_1 subset.eq W_1$.

  // TODO: Better "Proof" label
  Proof.\
  Let $v in W'_i$, then there exist a strategy $sigma_i$ on $G'$ the for player $i$ such that for any strategy $sigma_(1-i)$ for player $1-i$ on $G'$ the resulting play is winning for player $i$. Moreover after fixing the strategy $sigma_i$ the player $1-i$ has no way make the play to reach a vertex connected to an edge that's not included in the subgame, by definition of $W'_i$. Thus given any strategy for player $1-i$ in the full game, the resulting play will still be limited to the subgame, and will be won by player $i$. Hence $v in W_i$ and thus $W'_i subset.eq W_i$.
]

=== Graph simplification

In the local strategy iteration it may happen that we learn about the winner on a vertex that is not the one we are interested in. When this happens we will do a lot of wasted work in the subsequent valuations steps, since it will have to visit its edges again and again. We now propose a transformation that produces a compatible graph and reduces the amount of edges of vertices in the definitely winning sets, thus decreasing the amount of work that the valuation step needs to perform. Informally, the idea will be to replace all outgoing edges from vertices in a definitely winning set with one pointing to one of the four auxiliary vertices $w0$, $l0$, $w1$ or $l1$ in such a way that its winner is preserved and the graph remains bipartite.

#definition("simplified graph")[
  Let $G = (V'_0, V'_1, E, p)$ be the induced total parity game from $(V_0, V_1, E, p)$, let $G' = (G, U, E')$ be a partially expanded game with ${w0, l0, w1, l1} in U$ and let $v in (V_0 union V_1) sect U$. Let $W'_0$ and $W'_1$ be the definitely winning sets of $G'$. Then the simplified graph of $G'$ is $G'' = (V'_0 sect U, V'_1 sect U, E'', p')$ where:
  
  - if $v in V_0 sect W'_0$ then $E'' = E' without v E' union {(v, l1)}$;
  - if $v in V_0 sect W'_1$ then $E'' = E' without v E' union {(v, w1)}$;
  - if $v in V_1 sect W'_1$ then $E'' = E' without v E' union {(v, l0)}$;
  - if $v in V_1 sect W'_0$ then $E'' = E' without v E' union {(v, w0)}$;
]

// TODO: Are these needed or do we need proof?
#lemma("simplified graph bipartite")[
  TODO: Prove that the simplified graph is still bipartite
]

// TODO: Are these needed or do we need proof?
#lemma("simplified graph total")[
  TODO: Prove that the simplified graph is still bipartite
]

#theorem("simplified graph compatible")[
  TODO: Prove that the simplified graph is compatible with the partially expanded game it comes from.
]

- TODO: How to remove edges lazily in formulas (set atom to T/F)
- TODO: Exponential increase in expanded nodes
- TODO: (Maybe) Compute play profiles of expanded nodes
- TODO: (Maybe) Only consider unknown/improving vertices

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

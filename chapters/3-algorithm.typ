#import "../config/common.typ": *

// TODO: Better section title?
= Symbolic local algorithm

== Adapting the algorithm

Our goal will be to adapt and improve the local strategy iteration algorithm to solve systems of fixpoint equations expressed as parity games using the symbolic formulation.

=== Handling finite plays

The parity game formulation of a system of fixpoint equations admits positions where a player has no available moves, meaning it is not a total parity game. However the strategy improvement algorithm requires a total parity game, so we need to convert a generic parity game into a "compatible" total parity game that can be handled by it, for some definition of "compatible.

The way we do this transformation is by providing auxiliary vertices that will be used as successors for those vertices that do not have one, in particular we will add two vertices $w0$ and $w1$ representing vertices that are both controlled by and winning for respectively player 0 and 1. These will be used for vertices that have no successors, meaning they are losing for the player controlling them and thus need a successor that is controlled by and winning for the opposite player. $w0$ and $w1$ will in turn also need successors, and these will be respectively $l1$ and $l0$, representing vertices that are controlled by and losing for respectively player 1 and 0. The vertices $w0$ and $l1$ will thus form a forced cycle, as well as $w1$ and $l0$. This, along with priorities choosen as favourable for the player that should win these cycles, will guarantee that the winner will actually be the expected one.

#definition("induced total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. The induced total parity game of $G$ is the parity game $G' = (V'_0, V'_1, E', p')$ where:
  
  #baseline-list[
    - $V'_0 = V_0 union { w0, l0 }$

    - $V'_1 = V_1 union { w1, l1 }$

    - #box(baseline: 2em, $
    E' = E &union { (v, w_i) | i in {0,1} and v in V_(1-i) and v E = varempty } \ &union { (w0, l1), (l1, w0), (w1, l0), (l0, w1) }
    $)

    - #box(baseline: 2em, math.equation(block: true, $p'(v) = cases(
        p(v) & "if" v in V \
        0 & "if" v in { w_0, l_1 } \
        1 & "if" v in { w_1, l_0 }
      )$))
  ]
]

We now want to prove that this new parity game is "compatible" with the original one, for some definition of "compatible". In particular for our purposes we are interested in the new game preserving the winners for the vertices in the old game.

#definition("compatible parity games")[
  Let $G = (V_0, V_1, E, p)$ and $G' = (V'_0, V'_1, E', p')$ be two parity games. Let $W_0$ and $W_1$ be the winning sets for $G$ and $W'_0$ and $W'_1$ the winning sets for $G'$. We say that $G'$ is compatible with $G$ if $W_0 subset.eq W'_0$ and $W_1 subset.eq W'_1$.
]

#definition("strategy on induced total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. Let $sigma$ a strategy on $G$ for player $i$. $sigma$ induces the following $sigma'$ strategy on $G'$:
  $
    sigma'(v) = cases(
      sigma (v) & "if" v in V_i and v E != varempty \
      W_(1-i) & "if" v in V_i and v E = varempty \
      W_(1-i) & "if" v = L_i \
      L_(1-i) & "if" v = W_i
    )
  $
]

It can be observed that strategies on a parity game and those on its induced total game create a bijection. In fact notice that the condition $v in V_i and v E != varempty$ in the first case of $sigma'$ is equivalent to requiring $v in dom(sigma)$, meaning that restricting $sigma'$ to $dom(sigma)$ will result in $sigma$ itself.

The bijection is not only limited to this. It can be showed that strategies that are correlated in this bijection will also induce plays with the same winner.

#theorem("plays on induced strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. Let $sigma_0$ and $sigma_1$ be two strategies on $G$ and $sigma'_0$ and $sigma'_1$ the unique corresponding strategies on $G'$. Let $v in V_0 union V_1$ and consider the plays starting from $v_0$ on the instances $I = (G, sigma_0, sigma_1)$ and $I' = (G', sigma'_0, sigma'_1)$. The two plays have the same winner.

  // TODO: Better "Proof" label
  Proof. \
  We will prove that for all $i$ the play induced by $I$ is won by player $i$ if and only if the induced play by $I'$ is also won by player $i$:
  - $=>)$: We distinguish two cases on the play induced by $I$:
    - the play is infinite: $v_0 v_1 v_2 ... $, then every vertex is in $dom(sigma_i)$ for some $i$ and thus $sigma'_i$ are defined to be equal to $sigma_i$ and will induce the same play, which is won by player $i$;
    - the play is finite: $v_0 v_1 ... v_n$, with $v_n in V_(1-i)$ because the play is won by player $i$. For the same reason as the previous point the two induced plays are the same until $v_n$, which is not in $dom(sigma_(1-i))$ but is in $dom(sigma'_(1-i))$. The play induced by $I'$ is $v_0 v_1 ... v_n w_i l_(1-i) w_i ...$ which is also won by player $i$ because only the vertices $w_i$ and $l_(1-i)$ repeat infinitely often, and they have both priority favourable to player $i$.
  - $arrow.l.double \)$: We distinguish the following cases on the play induced by $I'$:
    - the play never reaches the $w_0, w_1, l_0$ or $l_1$ vertices: $v_0 v_1 v_2 ...$, then only the first case of $sigma'_i$ is ever used and thus every vertex is in $dom(sigma_i)$. Thus $I$ induces the same play, which is won by player $i$;
    - the play reaches $w_i$: $v_0 v_1 ... v_n w_i l_(1-i) w_i ...$, then $v_n$ is not in $dom(sigma_(1-i))$ and $I$ induces the finite play $v_0 v_1 ... v_n$ which is won by player $i$ because $v_n in V_(1-i)$ due to its successor being controlled by player $i$;
    - the play reaches $w_(1-i)$: this is impossible because it would be winning for player $1-i$, which contradicts the hypothesis;
    - the play reaches $l_i$ or $l_(1-i)$ before $w_i$ or $w_(1-i)$: this is impossible because the only edges leading to $l_i$ or $l_(1-i)$ start from $w_(1-i)$ and $w_i$.
]

#theorem("compatibility of induced total parity games")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (V'_0, V'_1, E', p')$ be the induced total parity game from $G$. Then $G'$ is compatible with $G$, that is $forall i. W_i subset.eq W'_i$.

  // TODO: Better "Proof" label
  Proof.\
  Let $v in W_i$, then there exist a winning strategy $sigma_i$ for player $i$. We claim that the induced strategy $sigma'_i$ for player $i$ on $G'$ is also winning. In fact consider any strategy $sigma'_(1-i)$ for player $1-i$ on $G'$, then it is induced by a strategy $sigma_(1-i)$ on $G$. We know that the play starting from $v$ on the instance $(G', sigma'_0, sigma'_1)$ is won by the same player as the play starting from $v$ on the instance $(G, sigma_0, sigma_1)$. Moreover since $sigma_i$ is a winning strategy for player $i$ we know that these plays are won by player $i$, thus $v in W'_i$ and so $W_i subset.eq W'_i$.
]

=== Generalizing subgames with subset of edges

The local strategy improvement algorithm gives a way to consider only a subset of the vertices, but still assumes all edges between such vertices to be known. However this is not true in the symbolic formulation, as the list of successors of vertices in $V_0$ is computed lazily, and this might include vertices already in the subgame. We thus have to update the local algorithm to handle this case by extending the idea of escape set. Instead of identifying those vertices that can reach the $U$-exterior we will instead identify those vertices that can reach an "unexplored" edge, that is an edge present in the full game but not in the subgame. We will call the vertices directly connected to such edges _incomplete vertices_. Note that the resulting set will be a superset of the $U$-exterior, since edges that lead outside $U$ cannot be part of the subgame.

// TODO: Make this fit
#definition("subgame")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $E' subset.eq E sect (U times U)$, then $G' = (V_0 sect U, V_1 sect U, E', p|_U)$, where $p|_U$ is the function $p$ with domain restricted to $U$, is a subgame of $G$. We will write $G' = (G, U, E')$ for brevity.
]

// TODO: Call this escape set again.
#definition("incomplete vertex")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. The set of incomplete vertices is $I_G (E') = { v | v E != v E' }$.
]

#definition("escape set (updated)")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma^*$ (resp. $E_tau^*$) be the transitive-reflexive closure of $E_sigma$ (resp. $E_tau$). The updated escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect I_G (E')$ (resp. $E_L^1 (v) = v E_tau^* sect I_G (E')$).
]

#theorem("definitive winning set sound")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. Let $L = (G|_U, sigma, tau)$ be an optimal instance of the subgame. Then $W'_0 subset.eq W_0$ and $W'_1 subset.eq W_1$.

  // TODO: Better "Proof" label
  Proof.\
  Let $v in W'_i$, then there exist a strategy $sigma_i$ on $G'$ the for player $i$ such that for any strategy $sigma_(1-i)$ for player $1-i$ on $G'$ the resulting play is winning for player $i$. Moreover after fixing the strategy $sigma_i$ the player $1-i$ has no way make the play to reach a vertex connected to an edge that is not included in the subgame, by definition of $W'_i$. Thus given any strategy for player $1-i$ in the full game, the resulting play will still be limited to the subgame, and will be won by player $i$. Hence $v in W_i$ and thus $W'_i subset.eq W_i$.
]

=== Expansion scheme

// TODO(prof): Cito testualmente Friedmann o inserisco riferimenti al paper?
In the local strategy iteration the expansion scheme is tasked with expanding the subgame by adding new nodes to it, in our adaptation it will instead add new edges to it. This does not however change much the logic behind it, since the expansion schemes defined in @friedmann_local are all based on picking vertices in the $U$-exterior or unexplored successors, which can be trivially replaced with picking incomplete vertices and unexplored edges.

However the resulting properties of the expansion scheme are not guaranteed to stay the same. For example the upper bound on the number of expansions grows from $O(|V|)$ to $O(|E|)$, since in the worse case each expansion adds one edge and they may all be necessary to determine the actual winner on the initial vertex. As shown in @friedmann_local, a big number of expansions might not be ideal because each will require at least one strategy iteration, which in the long run can end up being slower than directly running the global algorithm.

On the other hand a lazier expansion scheme can take better advantage of the ability to perform simplifications on symbolic moves, which allows to remove lot of edges in bulk. A more eager expansion scheme may instead visit all those edges, just to ultimately find out that they were all losing for the same reason. There is thus a tradeoff involved between expanding too much at once, which loses some of the benefits of using symbolic moves, and too little, which instead leads to too many strategy iterations.

In practice we will test our adaptation using a modified version of the symmetric expansion scheme from @friedmann_local. This scheme will pick an incomplete vertex and add one its unexplored edges to the subgame. If such edge leads to an unexplored vertex the expansion scheme will continue by picking an edge from such vertex and so on until an existing vertex is reached, re-establishing the total property of the graph.

// === Symbolic formulas simplification

// TODO: How to remove edges lazily in formulas (set atom to T/F)


== Improvements

=== Graph simplification

In the local strategy iteration it may happen that we learn about the winner on a vertex that is not the one we are interested in. When this happens we will do a lot of wasted work in the subsequent valuations steps, since it will have to visit its edges again and again. 
// TODO(Prof): Explain cosa?
We now propose a transformation that produces a compatible graph and reduces the amount of edges of vertices in the definitely winning sets, thus decreasing the amount of work that the valuation step needs to perform. Informally, the idea will be to replace all outgoing edges from vertices in a definitely winning set with one pointing to one of the four auxiliary vertices $w0$, $l0$, $w1$ or $l1$ in such a way that its winner is preserved and the graph remains bipartite.

#definition("simplified graph")[
  Let $G = (V'_0, V'_1, E', p)$ be the induced total parity game from $(V_0, V_1, E, p)$, let $G' = (G, U, E'')$ be a partially expanded game with ${w0, l0, w1, l1} in U$ and let $W'_0$ and $W'_1$ be the definitely winning sets of $G'$. Let $v in (V_0 union V_1) sect (W'_0 union W'_1)$, then $G$ can be simplified to the graph $(V'_0, V'_1, E''', p')$ where:
  
  - if $v in V_0 sect W'_0$ then $E''' = E' without v E'' union {(v, l1)}$;
  - if $v in V_0 sect W'_1$ then $E''' = E' without v E'' union {(v, w1)}$;
  - if $v in V_1 sect W'_1$ then $E''' = E' without v E'' union {(v, l0)}$;
  - if $v in V_1 sect W'_0$ then $E''' = E' without v E'' union {(v, w0)}$;
]

#theorem("simplified graph compatible")[
  TODO: Prove that the simplified graph is compatible with the original induced total parity game.
]

=== Computing play profiles of the expansion

Each game expansion is normally followed by a strategy iteration step, which computes the play profile of each vertex and then tries to improve the current strategy. We can notice however that the play profiles of all the vertices are known right before the expansion, and if we keep the current strategies fixed, both for player 0 and 1, then the newer vertices cannot influence the play profiles for the existing vertices, since the existing strategies will force any play to remain within the edges in the old subgame. Hence, we can compute the play profiles for the newer vertices in isolation, and only then determine if the existing strategies can be improved given the newer vertices.

In order to compute the play profile of the expanded vertices we need to distinguish two cases. In the first case the expansion stops by reaching an existing vertex, in which case the play profiles will be an extension of the play profile of that vertex, according to the play that starts from each of the expanded vertices and visits the other expanded vertices until it reaches the existing vertex. In the second case the expansion stops by reaching another vertex of the expansion, creating a loop, in which case the loop and the most relevant vertex of the loop must be determined, and the play profiles will be determined by looking at the path from each expanded vertex to the most relevant vertex of the loop.

By computing the play profiles after an expansion step it can be determined whether an improvement step can occur or not by comparing the play profiles of the strategy successor of the first expanded vertex with its successor in the expansion. If this does not lead to an improvement step then the expansion can continue, avoiding the cost of the strategy improvement step.

// TODO: Example is cwi where most of the ~2000 vertices in the graph are visited in this way

// TODO: more formal description?

=== Exponentially increasing expansion scheme

While lazier expansion schemes are intuitively better when paired with symbolic moves simplification, and the incremental play profiles computation helps often removes the need to perform an expensive valuation step, it can still happen that games fall into the worst case of expanding only a handful of edges in each iteration without being able to perform significant simplifications. This can be avoided by expanding more eagerly, like in the asymmetric expansion scheme for the local strategy improvement algorithm, but ideally we would like to be lazier when possible. We thus tried setting a minimum amount of edge to add to the graph before considering to perform a valuation step, and increasing it exponentially for each subsequent expansion. This will initially have the benefits of a lazy expansion scheme, due to not forcing to add many edges to the graph, but ultimately will only require a logarithmic number of expansions in the worst case, and with it the number of costly valuation steps. 

- TODO: proof on the maximum number of expansions?

- TODO: does this actually change complexity, or only in practice for "reasonable" inputs?

// TODO: Explain the final algorithm?

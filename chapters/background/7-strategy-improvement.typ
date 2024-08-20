#import "../../config/common.typ": *
#import "@preview/algorithmic:0.1.0"

== Local strategy iteration

=== Strategy iteration

Strategy iteration @jurdzinski_improvement is one of the oldest algorithms that computes the winning sets and the optimal strategies for the two players of a bipartite and total parity game. The algorithm starts with a strategy for player 0 and repeates _valuation_ phases, during which it computes a _play profile_ for each vertex, and _improvement_ phases, during which it uses such play profiles to improve the strategy. This continues until the strategy can no longer be improved, at which point it is guaranteed to be optimal.

We will start introducing some concepts that will help characterize how favourable a vertex is for a given player. We will start by giving the definition of a _relevance ordering_, which is a total order over the vertices where bigger vertices correspond to bigger priorities. This will be important in determining which vertices are more impactful on the winner of a play. We then define the sets of _positive and negative vertices_, which are a different way to partition the set of vertices. In particular the set of positive vertices contains vertices whose priority is even, and thus more favourable to player 0, while the negative vertices will be those with odd priority. We also introduce a _reward ordering_, which instead expresses how favourable to player 0 a vertex is. In particular a positive vertex has a bigger reward than a negative one. Positive vertices are also more rewarding if they have a bigger priority, while negative vertices are less rewarding in that case. Finally, the reward ordering is extended to sets of vertices, where the reward of the most relevant vertex decides which set is more rewarding.

#definition("relevance ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A relevance ordering $<$ is a total order that extends the partial order induced by the $p$ function. In particular $<$ is such that $forall u, v. p(u) < p(v) => u < v$.
]

#definition("positive and negative vertices")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. We define $V_+ = { v in V | p(v) "is even" }$ and $V_- = { v in V | p(v) "is odd" }$.
]

#definition("reward ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, and let $v, u in V$. We write $u lt.curly v$ when $u < v$ and $v in V_+$ or $v < u$ and $u in V_-$.
  $
    u lt.curly v <=> (u < v and v in V_+) or (v < u and u in V_-)
  $
]

#definition("reward ordering on sets")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and let $P, Q subset.eq 2^V$ be two different sets of vertices. We write $P lt.curly Q$ if the following holds:
  $
    P != Q and "max"_< P symmdiff Q in (P sect V_-) union (Q sect V_+)
  $
]

Intuitively $P lt.curly Q$ represents $P$'s reward being less than $Q$'s. The way this is determined is by looking at the vertices that are in either $P$ or $Q$ but not both, namely the symmetric set difference $P symmdiff Q$. The vertices that are in both are ignored because they will equally contribute to the reward of the two sets. From the symmetric difference it is then selected $v = max_< P symmdiff Q$, the greatest remaining vertex according to the relevance ordering. Then $P lt.curly Q$ holds when $v in P$ and $v in V_-$, representing the situation where $v$ is not favourable to player 0 and thus makes the reward of the left set worse, or when $v in Q$ and $v in V_+$, representing the situation where $v$ is favourable to player 0 and thus makes the reward of the right set better.

At the core of the algorithm there is the valuation phase computing the _play profiles_, which helps understanding how favourable a play is for each player. Moreover an ordering between play profiles is defined, with bigger values being more favourable to player 0 and lower ones being more favourable to player 1. In particular play profiles are based on three key values:

- the most relevant vertex that is visited infinitely often, which we will refer to as $w$, which directly correlates to the winner of the play;
- the vertices visited before $w$ that are more relevant than it;
- the number of vertices visited before $w$.

Recall that the game is total, thus every play is infinite, and plays induced by an instance that are infinite always consists of a prefix followed by a cycle. Thus in this case $w$ coincides with the most relevant vertex of the cycle that is reached in a play.

Intuitively in this context the last two values are linked to the chances that changing strategy would change either the value of $w$ or the cycle itself, thus more relevant vertices before $w$ or a longer prefix are more beneficial for the losing player.

#definition("play profile and valuation")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and $pi = v_0 v_1 ...$ a play on $G$. Let $w = max_< inf(pi)$ be the most relevant vertex that is visited infinitely often in the play and $alpha = { u in V | exists i in N. v_i = u and forall j < i. v_j != w }$ be the set of vertices visited before the first occurence of $w$. Let $P = alpha sect { v in V | v > w }$ and $e = |alpha|$. The play profile of the play $pi$ is the tuple $(w, P, e)$.

  Given an instance $(G, sigma, tau)$ a valuation $phi$ is a function that associates to each vertex the play profile $(w, P, e)$ of the play induced by the instance.
]

// TODO: This needs generic subgames and strategy restricted edges/game.
An algorithm is given in @jurdzinski_improvement that takes a graph restricted to a strategy for player 0 and computes an optimal strategy for player 1 along with with a valuation for them. The algorithm has a worst case complexity of $O(|V| times |E|)$.
// TODO: Explain reach and maximal/minimal_distances

#algorithmic.algorithm({
  import algorithmic: *
  Function($valuation$, args: ("H",), {
    For(cond: $v in V$, {
      State[$phi(v) = bot$]
    })
    For(cond: [$w in V$ (ascending order with respect to $lt.curly$)], {
      If(cond: $phi(w) = bot$, {
        State[$L = reach(H|_({v in V | v <= w}), w)$]
        If(cond: $E_H sect {w} times L != varempty$, {
          State[$R = reach(H, w)$]
          State[$phi|_R = subvaluation(H|_R, w)$]
          State[$E|_H = E|_H without (R times (V without R))$]
        })
      })
    })
    Return($phi$)
  })
  State[]
  Function($subvaluation$, args: ("K", "w"), {
    For(cond: $v in V_K$, {
      State[$phi_0 (v) = w$]
      State[$phi_1 (v) = varempty$]
    })
    For(cond: [$u in {v in V_K | v > w}$ (descending order with respect to $<$)], {
      If(cond: $u in V_+$, {
        State[$overline(U) = reach(K|_(V_K without {u}), w)$]
        For(cond: $v in V_K without overline(U)$, {
          State[$phi_1 (v) = phi_1 (v) union {u}$]
        })
        State[$E_K = E_K without ((overline(U) union {u}) times (V without overline(U)))$]
      })
      Else({
        State[$U = reach(K|_(V_K without {w}), u)$]
        For(cond: $v in U$, {
          $phi_1 (v) = phi_1 (v) union {u}$
        })
        State[$E_K = E_K without ((U without {u}) times (V without U))$]
      })
    })
    If(cond: $w in V_+$, {
      State[$phi_2 = maximaldistances(K, w)$]
    })
    Else({
      State[$phi_2 = minimaldistances(K, w)$]
    })
    Return($phi$)
  })
})

Given a valuation we are then interested in determining whether a strategy is optimal. It can be shown @jurdzinski_improvement that if there exist a winning strategy for a player then the _optimal_ strategy is winning, otherwise it must be losing. The problem thus reduces in determining whether the current player 0 strategy is optimal, and if not improve it until it is. This can be done by looking at the play profiles of the successors of each vertex: if one of them is greater than the one of the successor chosen by the current strategy then it is not optimal. In other words the optimal strategy chooses the successor with the greatest play profile. If the strategy is not optimal then a new strategy is determined by picking for each vertex the successor with the greatest play profile. Note however that this is not guaranteed to be optimal. In fact since the strategy has changed the valuation and play profiles must be recomputed, and hence might change and still make the new strategy non-optimal. It can however be shown @jurdzinski_improvement that each new strategy "improves" upon the previous one, and eventually this process will reach the optimal strategy. 

#definition("play profile ordering")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, and $(u, P, e)$ and $(v, Q, f)$ be two play profiles. Then we define:
  $
    (u, P, e) lt.curly (v, Q, f) <=> cases(
      & u lt.curly v \
      or ( & u = v and P lt.curly Q) \
      or ( & u = v and P = Q and u in V_- and e < f) \
      or ( & u = v and P = Q and u in V_+ and e > f)
    )
  $
]

#theorem("optimal strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, $sigma$ and $tau$ be two strategies for respectively player 0 and 1 and $phi$ a valuation function for $(G, sigma, tau)$. The strategy $sigma$ is optimal against $tau$ if $forall u in V_0. forall v in u E. phi(v) lt.curly.eq phi(sigma(u))$. Dually, $tau$ is optimal against $sigma$ if $forall u in V_1. forall v in u E. phi(tau(u)) lt.curly.eq phi(v)$.
]

// TODO: Small example of strategy iteration?

It has been proven @jurdzinski_improvement that the algorithm can require $O(Pi_(v in V_0) "out-deg"(v))$ improvement steps in the worst case. Intuitively this is because each of the $Pi_(v in V_0) "out-deg"(v)$ strategies for player 0 could end up being considered.

=== Local algorithm

The strategy improvement algorithm has the downside of requiring to visit the whole graph. In some cases this might be an inconvenience, as the graph could be very large but only a small portion may need to be visited to determine the winner of a specific vertex of interest. For an extreme example, consider a disconnected graph, in which case the winner of a vertex only depends on its connected component and not on the whole graph.

The local strategy iteration algorithm @friedmann_local fills this gap by performing strategy iteration on a _subgame_, a parity game defined as a subgraph of the main game, and providing a way to determine whether this is enough to infer the winner in the full game. It may happen that the winner is not immediately decidable, in which case the subgame would have to be _expanded_. To do this we will need to define what a subgame is, how to expand it and what is the condition that decides the winner on a vertex.


#definition([$U$-induced subgames])[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. The $U$-induced subgame of $G$, written $G|_U$, is a parity game $G' = (V_0 sect U, V_1 sect U, E sect (U times U), p|_U)$, where $p|_U$ is the function $p$ with domain restricted to $U$.
]

#definition("partially expanded game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = G|_U$ a subgame of $G$. If $G'$ is still a total parity game it is called a partially expanded game.
]

Given a partially expanded game, two optimal strategies and its winning sets, the local algorithm has to decide whether vertices winning for a player in this subgame are also winning in the full game. Recall that a strategy is winning for a player $i$ if any strategy for the opponent results in an induced play that is winning for $i$. However those plays being losing in the subgame do not necessarily mean that all plays in the full game will be losing too, as they might visit vertices not included in the subgame. Intuitively, the losing player might have a way to force a losing play for them to reach one of the vertices outside the subgame, called the _$U$-exterior_ of the subgame, and thus lead to a play that is not possible in the subgame. The set of vertices that can do this is called the _escape set_ of the subgame, and for such vertices no conclusions can be made. For the other vertices instead the winner in the subgame is also the winner in the full game and they constitute the definitely winning sets.

#definition($U$ + "-exterior")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. The $U$-exterior of $G|_U$, also written $D_G (U)$, is the set of successors of vertices in $G|_U$ that are not themselves in $G|_U$. That is:
  $
    D_G (U) = union.big_(v in U) v E sect (V without U)
  $
]

In order to define the concept of _escape set_ we will use the notion of _strategy restricted edges_. These are needed because we are interested in plays that are losing for a player, and to do that we have to restrict the moves of the opposing player to the ones represented by its optimal strategy. 

#definition("strategy restricted edges")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $sigma$ a strategy for player $i$ in $G$. The set of edges restricted to the strategy $sigma$ is $E_sigma = { (u, v) | u in V_i => sigma(u) = v }$.
]

#definition("escape set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $G|_U$ the induced subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma^*$ (resp. $E_tau^*$) be the transitive-reflexive closure of $E_sigma$ (resp. $E_tau$). The escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect D_G (U)$ (resp. $E_L^1 (v) = v E_tau^* sect D_G (U)$).
]

#definition("definitive winning set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $G|_U$ the induced subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an optimal instance of the subgame and let $phi$ be the valuation for this instance. The definitive winning sets $W'_0$ and $W'_1$ are defined as follows:
  $
    W'_0 &= { v in U | E_L^1 (v) = varempty and (phi(v))_1 in V_+ } \
    W'_1 &= { v in U | E_L^0 (v) = varempty and (phi(v))_1 in V_- }
  $
]

In pratice we will however not compute the full escape sets, but instead we will find for which vertices they are empty. We can do this by considering all the vertices in $U_i$ that can reach vertices in the unexplored part of the game. Then we compute the set of vertices that can reach said vertices when the edges are restricted according to the strategy for player $1-i$. This will result in the set of all vertices which have a non-empty escape set, so we just need to consider their complement when computing the definitive winning sets.

#lemma("definitive winning set soundness")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. Then $W'_0 subset.eq W_0$ and $W'_1 subset.eq W_1$.
]

// TODO: Spiega algoritmo (pseudocodice?)
Once a subgame is solved but no conclusion can be determined the subgame needs to be _expanded_, with the goal of reducing the escape sets and ultimately determing whether the vertex of interest is definitely winning or not. Two expansion schemes are provided in @friedmann_local, one called symmetric and the other asymetric. Both start by considering the player that wins the subgame from the vertex of interest and choosing one vertex in the escape set of the opponent, which cannot be empty. This vertex is then added to the subgame, and in order to keep it a total game the expansion phase must also add at least one of its successors and so on, until the graph becomes total again. The two schemes differ in this last step, as the asymmetric scheme will add one successor for player 0 vertices and all successors for player 1 vertices, while the symmetric scheme will always add one successor. Intuitively the asymmetric scheme assumes that player 0 will win the full game, while the symmetric scheme makes no such assumption and instead tries to limit the potentially expensive expansion. It was also proven in @friedmann_local that the asymmetric scheme will require at most $O(|V|^(|V_0|))$ iterations, while the symmetric one will require at most $O(|V| dot |V|^(|V_0|))$.

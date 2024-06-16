#import "../../config/common.typ": *

== Local strategy iteration

// TODO: Cite paper introducing it.

=== Strategy iteration

Strategy iteration @jurdzinski_improvement is an algorithm that computes the winning sets and the optimal strategies for the two players of a bipartite and total parity game. The algorithm starts with a strategy for player 0 and repeates _valuation_ phases, during which is computes a _play profile_ for each vertex, and _improvement_ phases, during which it uses such play profiles to improve the strategy. This continues until the strategy can no longer be improved and is guaranteed to be optimal.

// TODO: Something better?
We will now give some general notions that will simplify the following definitions.

#definition("positive and negative vertices")[
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
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and let $P, Q subset.eq 2^V$ be two different sets of vertices. Let $v = max_< P Delta Q$. We write $P lt.curly Q$ when $P$'s reward is less than $Q$'s, namely when $v in P$ and $v in V_-$, or when $v in Q$ and $v in V_+$.
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
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$ and $pi = v_0 v_1 ...$ a play on $G$. Let $w = max_< inf(pi)$ be the most relevant vertex that's visited infinitely often in the play and $alpha = { u in V | exists i in N. v_i = u and forall j < i. v_j != w }$ be the set of vertices visited before the first occurence of $w$. Let $P = alpha sect { v in V | v > w }$ and $e = |alpha|$. The play profile of the play $pi$ is the tuple $(w, P, e)$.

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

#lemma("optimal strategies")[
  Let $G = (V_0, V_1, E, p)$ be a parity game with a relevance ordering $<$, $sigma$ and $tau$ be two strategies for respectively player 0 and 1 and $phi$ a valuation function for $(G, sigma, tau)$.
  $sigma$ is optimal against $tau$ if $forall u in V_0. forall v in u E. phi(v) lt.curly.eq phi(sigma(u))$ and $tau$ is optimal against $sigma$ if $forall u in V_1. forall v in u E. phi(tau(u)) lt.curly.eq phi(v)$.
]

=== Local algorithm

The strategy improvement algorithm has the downside of requiring to visit the whole graph. In some cases this may be a problem, as the graph could be very large but only a small portion may need to be visited to solve the game.

// TODO: Example where this matters?

The local strategy iteration algorithm @friedmann_local fills this gap by performing strategy iteration on a _subgame_, a parity game performed on a subgraph of the main game, and providing a way to determine whether this is enough to infer the winner in the full game. It may happen that the winner is not immediately decidable, in which case the subgame would have to be _expanded_. To do this we will need to define what a subgame is, how to expand it and what is the condition that decides the winner on a vertex.

#definition("subgame")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $U subset.eq V$ and $E' subset.eq E sect (U times U)$, then $G' = (V_0 sect U, V_1 sect U, E', p|_U)$, where $p|_U$ is the function $p$ with domain restricted to $U$, is a subgame of $G$. We will write $G' = (G, U, E')$ for brevity.
]

#definition([$U$-induced subgames])[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $U subset.eq V$. The $U$-induced subgame of $G$, written $G|_U$, is the subgame $(G, U, E sect (U times U))$.
]

#definition("partially expanded game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G' = (G, U, E')$ a subgame of $G$. $G'$ is called a partially expanded game if it still is a total parity game.
]

Given a partially expanded game, two optimal strategies and its winning sets, the local algorithm has to decide whether vertices winning for a player in this subgame are also winning in the full game. Recall that a strategy is winning if any strategy of the opponent always induces a losing play for them. However those plays being losing in the subgame don't necessarily mean that all plays in the full game will be losing too, as they might visit vertices not included in the subgame. Intuitively, the losing player might have a way to force a play to reach one of the vertices just outside the subgame, called the _$U$-exterior_ of the subgame, and thus lead to a play that's not possible in the subgame. The set of vertices that can do this is called the _escape set_ of the subgame, and for such vertices no conclusions can be made, otherwise the winner in the subgame is also the winner in the full game.

#definition($U$ + "-exterior")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. The $U$-exterior of $G|_U$, also written $D_G (U)$, is the set of successors of vertices in $G|_U$ that are not themselves in $G|_U$. That is:
  $
    D_G (U) = union.big_(v in U) v E sect (V without U)
  $
]

#definition("strategy restricted edges")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $sigma$ any strategy in $G$. The set of edges restricted to the strategy $sigma$ is $E_sigma = { (u, v) | u in dom(sigma) => sigma(u) = v }$.
]

#definition("escape set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an instance of the subgame. Let $E_sigma^*$ (resp. $E_tau^*$) be the transitive-reflexive closure of $E_sigma$ (resp. $E_tau$). The escape set for player 0 (resp. 1) from vertex $v in U$ is the set $E_L^0 (v) = v E_sigma^* sect D_G (U)$ (resp. $E_L^1 (v) = v E_tau^* sect D_G (U)$).
]

// TODO: optimal instance?
#definition("definitive winning set")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. Let $L = (G|_U, sigma, tau)$ be an optimal instance of the subgame and let $phi$ be the valuation for this instance. The definitive winning sets $W'_0$ and $W'_1$ are defined as:
  $
    W'_0 &= { v in U | E_L^0 (v) = varempty and (phi(v))_1 in V_+ } \
    W'_1 &= { v in U | E_L^1 (v) = varempty and (phi(v))_1 in V_- }
  $
]

// TODO: W_0 / W_1 depend from the strategy?
#lemma("definitive winning set soundness")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and $G|_U$ a subgame of $G$. Then $W'_0 subset.eq W_0$ and $W'_1 subset.eq W_1$.
]

- TODO: Local algorithm: expansion
- TODO: Local algorithm: complexities (?)

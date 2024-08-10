#import "../../config/common.typ": *
#import "@preview/cetz:0.2.2": canvas, draw

== Parity games

Parity games @pg_ermeson @pg_zielonka are games with two players, 0 and 1, performed on directed graphs. A token is placed in a position, represented by nodes, and the two players move it along the edges of the graph. The set of nodes is partitioned in two sets and the player that chooses the move is determined by the subset in which the node for the current position is in. To each node is also associated a _priority_, represented by a natural number. The sequence of positions visited in a game is called _play_ and could be finite or infinite, depending on whether a position with no moves is reached or not. In case of a finite play the player who cannot move loses, otherwise if the play is infinite the priorities of the positions that are visited infinitely many times are considered: if the biggest one is even then player 0 wins, otherwise player 1 is the winner. Players are also sometimes called $exists$ and $forall$ or $lozenge$ and $square$ due to their meaning when using parity games for solving $mu$-calculus or fixpoints.

In @parity-example we can see an example of a parity game with 5 vertices. Circles represent vertices controlled by player 0 while squares represent vertices controlled by player 1. Each vertex is shown with its name and its priority. The vertices have been divided in two groups based on the winner on the vertices in them. The left one is winning for player 0 because from $v_0$ it can always go downwards to $v_1$, from which the only possible response possible for player 1 is to go back to $v_0$. Player 0 can thus force such play in which the higher infinitely visited priority is 2, hence the vertices are winning for player 0. In the right group a similar situation happens where player 1 can force any play to go through vertex $v_3$ infinitely often and thus winning the game. Notice that the edges from $v_0$ to $v_2$ and from $v_2$ to $v_1$ are never a good choice for the players, since they lead from a vertex that is winning for the player to one that is losing.

#let parity_game_example(withstrategy) = canvas({
  import draw: *

  set-style(content: (padding: .2), stroke: black)

  let node(pos, name, p, label) = {
    if p == 0 {
      circle(pos, name: name, radius: .65, stroke: black)
    } else {
      let (x, y) = pos
      rect((x - .65, y + .65), (x + .65, y - .65), name: name, radius: 0.05)
    }
    content(pos, label)
  }

  node((0, 0), "v0", 0, $v_0: 0$)
  node((0, -3.5), "v1", 1, $v_1: 2$)
  node((3.5, 0), "v2", 1, $v_2: 3$)
  node((3.5, -3.5), "v3", 0, $v_3: 5$)
  node((6.5, -1.75), "v4", 0, $v_4: 4$)

  let edge(ni, ai, nf, af, a, w) = {
    let pi = (name: ni, anchor: ai)
    let pf = (name: nf, anchor: af)
    let c = if withstrategy and w { red } else { black }
    bezier(pi, pf, (pi, 50%, a, pf), fill: none, stroke: c, mark: (end: ">"))
  }

  edge("v0", 235deg, "v1", 125deg, -20deg, true)
  edge("v1", 55deg, "v0", 305deg, -20deg, false)
  edge("v0", 0deg, "v2", 180deg, 0deg, false)
  edge("v2", 230deg, "v1", 20deg, 10deg, false)
  edge("v2", 270deg, "v3", 90deg, 0deg, true)
  edge("v3", -10deg, "v4", 260deg, -20deg, false)
  edge("v4", 190deg, "v3", 55deg, -20deg, false)
  edge("v4", 120deg, "v2", -5deg, -20deg, false)

  rect((-1, 1), (1, -4.5), radius: .5, stroke: .5pt)
  rect((2.5, 1), (7.5, -4.5), radius: .5, stroke: .5pt)
})

#figure(
  parity_game_example(false),
  caption: [Example of a parity game],
) <parity-example>

We will first introduce graphs and some convenient notation for them. Moreover we will also need a formal notion for infinitely recurring elements in a sequence in order to describe the winner of a parity game.

#notation("graph, successors and predecessors")[
  A simple graph is a pair $(V, E)$ where $V$ is the set of vertices and $E subset.eq V times V without {(v, v) | v in V}$ is the set of vertices. It is called finite if $V$ is finite.

  Given $u, v in V$ we write $u E v$ if $(u, v) in E$, that is if the graph contains the edge from $u$ to $v$.
  We also write $u E$ to denote the set of successors of $v$, i.e. ${ v in V | u E v }$, and $E v$ to denote the set of predecessors of $v$, i.e. ${ u in V | u E v }$.
]

#definition("infinitely recurring elements")[
  Let $pi = v_0 v_1 v_2 ...$ an infinite sequence of elements. We define $inf(pi)$ as the set of infinitely recurring elements of $pi$, that is $inf(pi) = { v | forall n. exists i >= n. v_i = v }$.
]

#definition("parity graph, parity game")[
  Let $(V, E)$ be a finite graph and $p: V -> bb(N)$ a so called priority function. A parity graph is a triple $G = (V, E, p)$.
  Let $V$ be partitioned into two sets $V_0$ and $V_1$. The tuple $G = (V_0, V_1, E, p)$ is a parity game.
]

#definition("play")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. Starting from a vertex $v_0 in V_0 union V_1$ we can build a potentially infinite sequence $pi = v_0 v_1 ...$ such that $forall i. v_i E v_(i+1)$. If the play is finite, that is $pi = v_0 v_1 ... v_n$, then $v_n E = varempty$ is also required. Such sequence is called a play.
]

#definition("winner of a play")[
  Let $G = (V_0, V_1, E, p)$ be a parity game and let $pi = v_0 v_1 ...$ be a play. The winner of $pi$ is:
  - if $pi$ is finite, that is $pi = v_0 v_1 ... v_n$ with $v_n in V_i$ then the winner is player $1-i$;
  - if $pi$ is infinite then consider $max inf(p(v_0) p(v_1) ...)$: if it is even the winner is player 0, otherwise it is player 1.
]

We will focus on parity games that are more restriced than this, which for convenience we will call _bipartite parity games_ and _total parity games_.
Bipartite parity games are games whose graph is bipartite, forcing players to perfectly alternate moves.
Total parity games instead require every vertex to have at least one successor, thus forcing every play to be infinite.

We will mostly assume bipartite parity games, while we will show that we can convert any parity game to a compatible total parity game.

#definition("bipartite parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. It is also a bipartite parity game if the graph $(V_0, V_1, E)$ is bipartite, that is $forall v in V_i. v E sect V_i = varempty$.
]

#definition("total parity game")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. It is also a total parity game if every vertex has at least one successor, that if $forall v in V_0 union V_1. v E != varempty$.
]

=== Strategies

By the well-known determinacy of parity games @pg_ermeson @pg_zielonka we know that each vertex is winning for exactly one of the two players, that is that player can force every play to be winning for them. Moreover it is known that the winning player also has a so-called memoryless winning strategy, that is a way to choose the next vertex in the play without considering the previous ones such that any resulting play is winning for them. From now on we will focus only on strategies and plays induced by strategies, as they are finite and easier to reason about.

#definition("strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A (memoryless) strategy for player $i$ is a function from $v in V_i$ such that $v E != varempty$ to $v E$.
]

#definition("strategy induced instance")[
  Let $G = (V_0, V_1, E, p)$ be a parity game, $sigma$ be a strategy for player 0 and $tau$ be a strategy for player 1. An instance of the game $G$ induced by the strategies $sigma$ and $tau$ is a tuple $(G, sigma, tau)$.

  Given a starting vertex $v_0 in V_0 union V_1$ an instance also uniquely defines a play, called an induced play, where if $v_i E != varempty$ then $v_(i+1) = sigma(v_i)$ if $v_i in V_0$ and $v_(i+1) = tau(v_i)$ if $v_i in V_1$, otherwise the play is finite and stops at $v_i$.
]
  
// TODO: Do we give a shorthand syntax to such plays?
It can be proven that if such play is infinite then it will eventually reach a cycle and repeatedly visit those vertices in the same order, that is the play will be $v_0 ... v_k v_(k+1) ... v_n v_(k+1) ... v_n ...$.

#definition("winning strategy")[
  Let $G = (V_0, V_1, E, p)$ be a parity game. A strategy $sigma_i$ for player $i$ is called winning on vertex $v$ if for any strategy $sigma_(1-i)$ for the opposing player, the play starting from vertex $v$ in the instance $(G, sigma_0, sigma_1)$ is winning for player $i$.
]

#lemma("determinacy of parity games")[
  Given a parity game $G = (V_0, V_1, E, p)$, for every vertex $v in V_0 union V_1$ one and only one of the players can force a winning play from $v$. The set of vertices $V$ can thus be partitioned in two *winning sets* $W_0$ and $W_1$ of the vertices where player 0 (resp. player 1) has a winning strategy starting from vertices in that set.
]

For example in the parity game in @parity-strategy-example the winning strategy for player 0 on vertex $v_0$ would be going to the vertex $v_1$, while for player 1 on vertex $v_2$ it would be going to the vertex $v_3$. For all the other vertices the strategy is not relevant, since it will always be losing for them.

#figure(
  parity_game_example(true),
  caption: [Example of a parity game along with its winning strategies],
) <parity-strategy-example>

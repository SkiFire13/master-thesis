#import "../../config/common.typ": *
#import "@preview/cetz:0.2.2": canvas, draw

== Partial orders, lattices and monotone functions

We start by defining what is a (complete) lattice and introducing some related concepts. This will be fundamental for defining systems of fixpoint equations, as their domain and codomain will be lattices. Moreover we are interested in least and greatest fixpoints, which intristically require a concept of order.

#definition("partial order, poset")[
  Let $X$ a set. A partial order $sub$ is a binary relation on $X$ which satisfies the following properties for all $x, y, z in X$:
  - (Antisymmetry): if $x sub y$ and $y sub x$ then $x = y$;
  - (Reflexivity): $x sub x$;
  - (Transitivity): if $x sub y$ and $y sub z$ then $x sub z$.

  A partially ordered set (poset, for short) is a pair $(X, sub)$.
]

A common example of poset is $(bb(N), <=)$, the set of natural numbers, and $<=$ is the standard order relation.

// TODO: Preorder?
#example("Posets and Hasse diagrams")[
  Posets can conveniently be visualized using _Hasse diagrams_, like the ones in @poset-example. In such diagrams lines connecting two elements represent the one on top being greater than the one on the bottom. Lines that could be obtained by transitivity are instead left implicit due to the fact that the diagram represents a valid poset.

  #let poset_example = canvas({
    import draw: *

    set-style(content: (padding: .2), stroke: black)

    let node(pos, name, label) = content(pos, label, name: name)

    content((-2, -4), $P$)
    node((-4, 0), "x", $x$)
    node((-2, 0), "y", $y$)
    node((-3, -2), "w", $w$)
    node((-3, -4), "z", $z$)
    line("x", "w")
    line("y", "w")
    line("z", "w")

    content((3, -4), $L$)
    node((1.5, 0), "top", $top$)
    node((0, -2), "a", $a$)
    node((2.25, -1.25), "b", $b$)
    node((1.5, -2.5), "c", $c$)
    node((3, -2.5), "d", $d$)
    node((1.5, -4), "bot", $bot$)
    line("top", "a")
    line("top", "b")
    line("a", "bot")
    line("b", "c")
    line("b", "d")
    line("c", "bot")
    line("d", "bot")

    content((7, -4), $bb(N)_omega$)
    node((6, 0), "omega", $omega$)
    node((6, -1.6), "2", $2$)
    node((6, -2.8), "1", $1$)
    node((6, -4), "0", $0$)
    line("omega", "2", stroke: (dash: "densely-dotted"))
    line("2", "1")
    line("1", "0")

    content((9, -4), $bb(B)$)
    node((9, -1), "tt", $tt$)
    node((9, -3), "ff", $ff$)
    line("tt", "ff")
  })

  #figure(
    poset_example,
    caption: [Hasse diagrams of four posets],
  ) <poset-example>
]

#definition("join and meet")[
  Let $(X, sub)$ be a poset and $S subset.eq X$. The meet (respectively join) of $S$, written $meet S$ (resp. $join S$), is the smallest (resp. greatest) element of $X$ that is bigger (resp. smaller) or equal to every element in $S$. Formally:
  - (Meet): $forall s in S. s sub meet S$ and $forall t in X. forall s in S. s sub t => meet S sub t$
  - (Join): $forall s in S. join S sub s$ and $forall t in X. forall s in S. t sub s => t sub join S$
]

For example in @poset-example, in the poset $L$ the join between $c$ and $d$, that is $join {c, d}$, is $b$, while the join between $a$, $c$ and $d$ is $join {a, c, d} = top$.

Meet and join do not always exist, for example in the poset $P$ the join between $x$ and $y$ does not exist because there is no element that is greater than both of them. It can however be proven that when a join or meet exists it is unique. For our purposes we will however be interested in posets where meet and join always exists, also commonly called _lattices_. The poset $P$ is thus not a lattice, while $L$, $bb(N)_omega$ and $bb(B)$ are all lattices.

#definition("complete lattice")[
  Let $(L, sub)$ be a poset. It is also a lattice if meet and join exist for every pair of elements, that is given $x, y in L$ both $meet {x, y}$ and $join {x, y}$ are defined.
  It is a complete lattice if meet and join exist for every subset, that is given $S subset.eq L$ both $meet S$ and $join S$ are defined.
]

Observe that every complete lattice $L$ has a smallest element, called the _bottom_ element $bot = meet varempty$, and a largest element, called the _top_ element $top = join L$. In particular, a complete lattice cannot be empty. For example in the three lattices in @poset-example the top elements would be $top$, $omega$ and $tt$, while the bottom elements would be $bot$, $0$ and $ff$. 

From now on we will work with complete lattices. For most examples we will however use finite lattices, which can be proved to always be complete lattices.

#lemma("finite complete lattices")[
  Let $(L, sub)$ be a finite lattice, that is a lattice where $L$ is a finite set. Then it is also a complete lattice.
]

In @poset-example both $L$ and $bb(B)$ are finite complete lattices. In particular $bb(B)$ is called the _boolean lattice_, since it contains the two boolean literals $tt$ and $ff$ and its join and meet operators are respectively the $or$ and $and$ operators. The $bb(N)_omega$ lattice is instead an infinite complete lattice, since it contains all natural numbers equipped with a top element $omega$. Note that the plain set of natural numbers $bb(N)$ is not a complete lattice because $join bb(N)$ is not defined, while in $bb(N)_omega$ it would be $omega$.

#definition("powerset")[
  Let $X$ be a set. Its powerset, written $2^X$, is the set of all subsets of $X$, that is $2^X = {S | S subset.eq X}$.
]

#example("powerset lattice")[
  Given a set $X$, the pair $(2^X, subset.eq)$ is a complete lattice.
  
  The $join$ and $meet$ operations are respectively the union $union$ and intersection $sect$ operations on sets, while the $top$ and $bot$ elements are respectively $X$ and $varempty$.
  
  #let powerset_example = canvas({
    import draw: *

    set-style(content: (padding: .2), stroke: black)

    let node(pos, name, label) = content(pos, label, name: name)

    node((2, 0), "top", ${a, b, c}$)

    node((0, -1.5), "ab", ${a, b}$)
    node((2, -1.5), "ac", ${a, c}$)
    node((4, -1.5), "bc", ${b, c}$)
    
    node((0, -3), "a", ${a}$)
    node((2, -3), "b", ${b}$)
    node((4, -3), "c", ${c}$)

    node((2, -4.5), "bot", $varempty$)

    line("ab", "top")
    line("ac", "top")
    line("bc", "top")

    line("a", "ab")
    line("a", "ac")

    line("b", "ab")
    line("b", "bc")

    line("c", "ac")
    line("c", "bc")

    line("bot", "a")
    line("bot", "b")
    line("bot", "c")
  })

  #figure(
    powerset_example,
    caption: [Hasse diagram of a powerset lattice],
  ) <powerset-example>
]

When we will later characterize the solutions of a system of fixpoint equations it will be convenient to consider a basis of the lattice involved. Intuitively a basis is a subset of elements which allows to express any other element as a join of a subset of such basis.

#definition("basis")[
  Let $(L, sub)$ be a lattice. A basis is a subset $B_L subset.eq L$ such that all elements of $L$ can be defined by joining subsets of the basis, that is $forall l in L. l = join { b in B_L | b sub l }$.
]

To give an example of a basis, consider the $L$ lattice in @poset-example. A basis for it is the set $B_L = {a, c, d}$, where we can express the other elements with $bot = join varempty$, $b = join {c, d}$ and $top = join {a, c, d} = join {a, c} = join {a, d}$. Note that there may be more than one way to obtain an element by joining a subset of a basis, as shown with $top$. The boolean lattice $bb(B)$ instead admits the simple basis ${ tt }$, since $ff = join varempty$ and $tt = join { tt }$. Another basis that we will use often is the basis of a powerset lattice, which we will now define.

#definition("basis of powerset", label: <powerset-basis>)[
  Given a set $X$, a basis of the poset $(2^X, subset.eq)$ is the set of singletons $B_(2^X) = { {x} | x in X }$.
]

We now also define the concept of upward-closed set and upward-closure. This concept will become important later on.

#definition("upward-closed set")[
  Let $(X, sub)$ be a poset and $U subset.eq X$. $U$ is an upward-closed set if $forall x, y in X$, if $x in U$ and $x sub y$ then $y in U$.
]

#definition("upward-closure")[
  Let $(L, sub)$ be a lattice and $l in L$. The upward-closure of $l$ is $up l = { l' in L | l sub l' }$.
]

It can be proven that the upward-closure of a set is an upward-closed set.

#definition("fixpoint")[
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a function. Any element $x in X$ such that $f(x) = x$ is a fixpoint of $f$.
]

Given a function $f : L -> L$ where $(L, sub)$ is a complete lattice, it is not guaranteed that a fixpoint exists. However if we restrict ourself to _monotone_ functions, then by the Knaster-Tarski theorem @tarski there exists at least one fixpoint. Moreover the set of all fixpoints is also a complete lattice, which guarantees the existence and uniqueness the least and greatest fixpoints.

#definition("monotone function")[
  Let $(X, sub)$ be a poset and $f: X -> X$ a function. $f$ is monotone if $forall x, y in X. x sub y => f(x) sub f(y)$
]

#theorem[Knaster-Tarski @tarski][
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a monotone function. The set of fixpoint of $f$ forms a complete lattice with respect to $sub$.

  The least fixpoint of $f$, written $lfp f$, is the bottom element of such lattice, while the greatest fixpoint of $f$, written $gfp f$, is the top element.
]

Kleene iteration @kleene also gives us a constructive way to obtain a least or greatest fixpoint by repeatedly iterating a function starting from the least or greatest element of the lattice. However it should be noted that it may not be efficient enough or even possible to compute a fixpoint in such a way, because it may require too many iterations (potentially an infinite amount in case of non-finite lattices) or because representing the actual solution may take too much space, and we are interested only in some specific characteristics of it.

// TODO: Continuous function o iterazione transfinita.
#theorem[Kleene iteration @kleene][
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a continuous function. Consider the ascending chain $bot sub f(bot) sub f(f(bot)) sub dots.h.c sub f^n (bot) sub dots.h.c$, it converges to $lfp f$. In other words, $lfp f = join { f^n (bot) | n in bb(N) }$. Similarly $gfp f = meet { f^n (top) | n in bb(N) }$.
]

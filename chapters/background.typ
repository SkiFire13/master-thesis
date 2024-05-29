#let environment(name) = {
  let env_counter = counter(name)
  (subject, body) => block(inset: (y: 5pt))[
    *#name #env_counter.step() #env_counter.display()*
    (#subject).
    _#(body)_
  ]
}

#let definition = environment("Definition")
#let lemma = environment("Lemma")
#let example = environment("Example")
#let notation = environment("Notation")

#let sub = math.class("relation", sym.subset.eq.sq)
#let meet = math.class("unary", sym.sect.sq)
#let join = math.class("unary", sym.union.sq)

#let lfp = math.class("unary", sym.mu)
#let gfp = math.class("unary", sym.nu)

#let tup(a) = math.bold(a)
#let range(end) = math.underline(end)
#let XX = math.bold("X")

#let syseq(x) = math.lr(sym.brace.l + block(math.equation(x, block: true, numbering: none)))
#let feq(kind) = math.class("relation", math.attach("=", br: kind))
#let sol = math.op("sol")

#let varempty = text(font: "", sym.emptyset)
#let eq-columns(..cols) = stack(
  dir: ltr,
  h(1fr),
  ..cols.pos().map(align.with(horizon)).intersperse(h(1fr)),
  h(1fr),
)

#set list(indent: 0.5em)
#show math.equation: it => {
  show ".": math.class("punctuation", ".")
  it
}

= Background

In this chapter we give an overview of the theoretical background used in the rest of this thesis.
// TODO: Anticipate arguments?

== Lattices

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

Meet and join don't always exist, but when they do it can be proven that they are unique. We will however work with posets where they always exist for our purposes.

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

#definition("powerset")[
  Let $X$ be a set. Its powerset, written $2^X$, is the set of all subsets of $X$, that is $2^X = {S | S subset.eq X}$.
]

#example("powerset lattice")[
  Given a set $X$, the pair $(2^X, subset.eq)$ is a complete lattice.
]

#definition("basis")[
  Let $(L, sub)$ be a lattice. A basis is a subset $B_L subset.eq L$ such that all elements of $L$ can be defined by joining subsets of the basis, that is $forall l in L. l = join { b in B_L | b sub l }$.
]

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

// TODO: Kleene iteration, not feasible

== Tuples

In order to define systems of fixpoint equations we'll need to refer to multiple equations/variables/values together, and to do that we'll use tuples. We introduce here some notations to better distinguish tuples from other values.

#definition("set of tuples")[
  Let $A$ be a set. The set of $n$-tuples of $A$ is $A^n$.
]

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

In order to describe the meaning of such system of fixpoint equations we'll need a few more notions. We will mostly assume that given a system all the variables will be named $x_i$ for $i in range(n)$.

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

== $mu$-calculus
// TODO: Examples with mu-calculus

== Parity games
// TODO: Equivalence with parity game

== Selections and symbolic formulation
// TODO: Selections and moves as formulas

== Local strategy iteration
// TODO: Local strategy iteration

// TODO: (For chapter after background) integrating formulas with local strategy iteration

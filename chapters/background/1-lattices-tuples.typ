#import "../../config/common.typ": *

== Partial orders, lattices and monotone functions

We will first define what is a lattice and the related concept. This will be fundamental for defining systems of fixpoint equations, as their domain and codomain will be lattices. Moreover we are interested in least and greatest fixpoints, which intristically require a concept of order.

#definition("partial order")[
  Let $X$ a set. A partial order $sub$ is a binary relation on $X$ which satisfies the following properties for all $x, y, z in X$:
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

Meet and join do not always exist, but when they do it can be proven that they are unique. For our purposes we will however be interested in posets where meet and join always exists, also called lattices.

#definition("lattice")[
  Let $(L, sub)$ be a poset. It is also a lattice if meet and join exist for every pair of elements, that is given $x, y in L$ both $meet {x, y}$ and $join {x, y}$ are defined.
]

// TODO: Bottom and Top

#definition("complete lattice")[
  Let $(L, sub)$ be a lattice. It is also a complete lattice if meet and join exist for every subset, that is given $S subset.eq L$ both $meet S$ and $join S$ are defined.
]

#lemma("finite complete lattices")[
  Let $(L, sub)$ be a finite lattice, that is a lattice where $L$ is a finite set. Then it is also a complete lattice.
]

// TODO: Do we _always_ work with finite lattices or do we use infinite ones too?
From now on we will work with finite, and thus complete, lattices.

// TODO: Image example of complete lattice?

#definition("powerset")[
  Let $X$ be a set. Its powerset, written $2^X$, is the set of all subsets of $X$, that is $2^X = {S | S subset.eq X}$.
]

#example("powerset lattice")[
  Given a set $X$, the pair $(2^X, subset.eq)$ is a complete lattice.
]

// TODO: Image example of powerset lattice

When we will later characterize the solutions of a system of fixpoint equations it will be convenient to consider a basis of the lattice involved. Intuitively a basis allows to express any element of a lattice as a join of all the basis elements that are under the given element.

#definition("basis")[
  Let $(L, sub)$ be a lattice. A basis is a subset $B_L subset.eq L$ such that all elements of $L$ can be defined by joining subsets of the basis, that is $forall l in L. l = join { b in B_L | b sub l }$.
]

// TODO: Image example of basis of non-powerset

#example("basis of powerset")[
  Given a set $X$, a basis of the poset $(2^X, subset.eq)$ is the set of singletons $B_(2^X) = { {x} | x in X }$.
]

// TODO: upward-closure?

Given any function it is not guaranteed that a fixpoint exists. However if we restrict ourself to _monotone_ functions, then by the Knaster-Tarski theorem @tarski there exists at least one fixpoint, moreover the set of all fixpoints is also a complete lattice, which guarantees the existance and uniqueness the least and greatest fixpoints.

#definition("monotone function")[
  Let $(X, sub)$ be a poset and $f: X -> X$ a function. $f$ is monotone if $forall x, y in X. x sub y => f(x) sub f(y)$
]

#definition("fixpoint")[
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a monotone function. Any element $x in X$ such that $f(x) = x$ is a fixpoint of $f$. \
  The least fixpoint of $f$, written $lfp f$, is the smallest of such elements, while the greatest fixpoint of $f$, written $gfp f$, is the biggest.
]

#lemma("Knaster-Tarski")[
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a monotone function. The set of fixpoint of $f$ forms a complete lattice with respect to $sub$.
]

Kleene iteration @kleene also gives us a constructive way to obtain a least or greatest fixpoint by repeatedly iterating a function starting from the least or greatest element of the lattice. However it should be noted that it may not be efficient enough or even possible to compute a fixpoint is such a way, be it because it requires too many iterations (potentially an infinite amount in case of non-finite lattices) or because representing the actual solution takes too much space, and we're interested only in some specific characteristics of it.

// TODO: Ok simplified version?
#lemma("Kleene iteration")[
  Let $(X, sub)$ be a complete lattice and $f: X -> X$ a monotone function. Consider the ascending chain $bot sub f(bot) sub f(f(bot)) sub dots.h.c sub f^n(bot) sub dots.h.c$, it converges to $lfp f$. In other words, $lfp f = join { f^n (bot) | n in bb(N) }$. Similarly $gfp f = meet { f^n (top) | n in bb(N) }$.
]

== Tuples

In order to define systems of fixpoint equations we will need to refer to multiple equations/variables/values together, and to do that we will use $n$-tuples. We now give a small introduction to them, along with some convenient notation for referring to them or their elements and constructing new ones.

#definition([set of $n$-tuples])[
  Let $A$ be a set. The set of $n$-tuples of $A$ is $A^n$.
]

#notation([$n$-tuple])[
  Let $A^n$ be a set of $n$-tuples. We will refer to its elements using boldface lowercase letters, like $tup(a)$. Given $tup(a) in A^n$ we will refer to its $i$-th element with the non-boldface $a_i$.
]

#notation("concatenation")[
  Let $tup(a_1), ..., tup(a_k)$ be either $n$-tuples or single elements of $A$. The notation $(tup(a_1), ..., tup(a_k))$ represents a $n$-tuple made by concatenating the elements in the tuples $tup(a_1), ..., tup(a_k)$. Single elements are considered as $1$-tuples for this purpose.
]

We will also often use ranges over natural numbers, typically in order to index each element of a tuple.

#notation("range")[
  We will refer to the set ${ 1, ..., n }$ with the shorthand $range(n)$.
]

// TODO: tuple range?

// TODO: define pointwise order (if needed)
#import "../../config/common.typ": *

== Tuples

In order to define systems of fixpoint equations we will need to refer to multiple equations/variables/values together, and to do that we will use $n$-tuples. We now introduce some basic notions regarding tuples, along with some convenient notation for referring to them or their elements and constructing new ones.

#definition([set of $n$-tuples])[
  Let $A$ be a set. Given $n >= 1$ the set of $n$-tuples of $A$, written $A^n$, is inductively defined as $A^0 = { () }$, $A^1 = A$ and $A^(n+1) = A times A^n$.
]

#notation([$n$-tuple])[
  Let $A^n$ be a set of $n$-tuples. We will refer to its elements using boldface lowercase letters, like $tup(a)$. Given $tup(a) in A^n$ we will refer to its $i$-th element with the non-boldface $a_i$.
]

#notation("concatenation")[
  Let $tup(a_1), ..., tup(a_k)$ be either $n$-tuples or single elements of $A$. The notation $(tup(a_1), ..., tup(a_k))$ represents a $n$-tuple obtained by concatenating the elements in the tuples $tup(a_1), ..., tup(a_k)$. Single elements are considered as $1$-tuples for this purpose.
]

We will also often refer to intervals over natural numbers, typically in order to index the elements of a tuple.

#notation("range")[
  We will refer to the set ${ 1, ..., n }$ with the shorthand $range(n)$.
]

#definition("pointwise order")[
  Let $(X, sub)$ be a poset. The pointwise order $psub$ on $X^n$ is defined, for $tup(x), tup(x') in X^n$, by $tup(x) psub tup(x')$ if $forall i in range(n). x_i sub x'_i$.

  It can be proven that $(X^n, psub)$ is also a poset. Moreover if $(X, sub)$ is a (complete) lattice then $(X^n, psub)$ is also a (complete) lattice, where $join tup(X) = (join X_1, join X_2, ..., join X_n)$ and similarly for $meet tup(X)$.
]

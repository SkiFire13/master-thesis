#import "../../config/common.typ": *

== Systems of fixpoint equations

#definition("system of fixpoint equation")[
  Let $(L, sub)$ be a complete lattice. A system of fixpoint equations $E$ is a system of the following shape:

  $
    syseq(
      x_1 &feq_eta_1 &f_1 &(x_1, ..., x_n) \
      x_2 &feq_eta_2 &f_2 &(x_1, ..., x_n) \
          &#h(0.3em)dots.v \
      x_n &feq_eta_n &f_n &(x_1, ..., x_n) \
    )
  $

  For all $i in range(n)$, $x_i in L$ and $f_i : L^n -> L$ is a monotone function. $eta_i$ is either $mu$ or $nu$, representing either a least or a greatest fixpoint equation.
]

#notation("system of fixpoint equations as tuple")[
  The above system of fixpoint equations can be written as $tup(x) feq_tup(eta) tup(f)(tup(x))$, where:
  - $tup(x) = (x_1, ..., x_n)$;
  - $tup(f) = (f_1, ..., f_n)$ but also seen as $tup(f): L^n -> L^n$ with $tup(f)(x_1, ..., x_n) = (f_1(x_1), ..., f_n (x_n))$;
  - $tup(eta) = (eta_1, ..., eta_n)$.
]

// TODO: tup(f) monotone according to pointwise order? Is it useful?

#notation("empty system of fixpoint equations")[
  A system of equations with no equations or variables is conveniently written as $emptyset$.
]

In order to describe the meaning of such system of fixpoint equations we will need a few more notions. We will mostly assume that given a system all the variables will be named $x_i$ for $i in range(n)$.

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
      x_1 &feq_mu x_1 union x_2 \
      x_2 &feq_nu x_1 sect x_2 \ 
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
      x_1 &feq_nu x_1 sect x_2 \
      x_2 &feq_mu x_1 union x_2 \
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

#import "../../config/common.typ": *

== Systems of fixpoint equations

// TODO: Relation to nested fixpoints?

We will now define what is a system of fixpoint equations and what is its solution, following the definition given in @baldan_games. Intuitively this will be very similar to a normal system of equations, except for the fact that each equation is interpreted as a fixpoint equation. Since there can be more than one fixpoint we will also need to specify which kind of fixpoint the equation refers to, which we will do by using respectively the symbols $lfp$ and $gfp$ in subscript after the equal sign to denote the fact that we refer to the least or greatest fixpoint, respectively.

#definition("system of fixpoint equation")[
  Let $(L, sub)$ be a complete lattice. A system of fixpoint equations $E$ over $L$ is a system of the following shape:

  $
    syseq(
      x_1 &feq_eta_1 &f_1 &(x_1, ..., x_n) \
      x_2 &feq_eta_2 &f_2 &(x_1, ..., x_n) \
          &#h(0.3em)dots.v \
      x_n &feq_eta_n &f_n &(x_1, ..., x_n) \
    )
  $

  where $forall i in range(n)$, $f_i : L^n -> L$ is a monotone function and $x_i$ ranges over $L$. Each subscript $eta_i$ must be either $mu$ or $nu$, representing respectively a least or a greatest fixpoint equation.
]

#notation("system of fixpoint equations as tuple")[
  The above system of fixpoint equations can be written as $tup(x) feq_tup(eta) tup(f)(tup(x))$, where:
  - $tup(x) = (x_1, ..., x_n)$;
  - $tup(f) = (f_1, ..., f_n)$ but also seen as $tup(f): L^n -> L^n$ with $tup(f)(x_1, ..., x_n) = (f_1 (x_1), ..., f_n (x_n))$;
  - $tup(eta) = (eta_1, ..., eta_n)$.
]

#notation("empty system of fixpoint equations")[
  A system of equations with no equations or variables is conveniently written as $varempty$.
]

#definition("substitution")[
  Let $(L, sub)$ be a complete lattice and $E$ be a system of $n$ fixpoint equations over $L$ and variables $x_i$ for $i in range(n)$. Let $j in range(n)$ and $l in L$. The substitution $E[x_j := l]$ is a new system of equation where the $j$-th equation is removed and any occurrence of the variable $x_j$ in the other equations is replaced with the element $l$.
]

We can now define the solution for a system of fixpoint equations recursively, starting from the last variable, which is replaced in the rest of the system by a free variable representing the fixed parameter. Then one obtains a parametric system with one equation less. This is inductively solved and its solution, which is a function of the parameter, is replaced in the last equation. This produces a fixpoint equation with a single variable, which can be solved to determine the value of the last variable.

// TODO: This is not sure
// Intuitively this could be seen as considering the lattice L^n of $n$-tuples ordered according to the pointwise extension of $sub$, and the monotone function $tup(f)$ over them. The fixpoints of this function will then form a lattice, but we are interested only in one of them. Starting from the $n$-th equation and going backward, we will iteratively restrict this lattice to only those elements where $x_i$ is the least or the greatest of all fixpoints, depending on whether the $i$-th equation is a least of greatest fixpoint. This step will fix that element of the solution, and repeating it for every equation will yield the final unique solution.

#definition("solution")[
  Let $(L, sub)$ be a complete lattice and $E$ be a system of $n$ fixpoint equations over $L$ and variables $x_i$ for $i in range(n)$. The solution of $E$ is $s = sol(E)$, with $s in L^n$ inductively defined as follows:

  $
    sol(varempty) &= () \
    sol(E) &= (sol(E[x_n := s_n]), s_n)
  $

  where $s_n = eta_n (lambda x. f_n (sol(E[x_n := x]), x))$.
]

#example("solving a fixpoint system", label: <system-example>)[
  Consider the following system of fixpoint equations $E$ over the boolean lattice $bb(B)$:
  $
    syseq(
      x_1 &feq_mu x_1 or x_2 \
      x_2 &feq_nu x_1 and x_2 \ 
    )
  $

  To solve this system of fixpoint equations we apply the definition of its solution, getting $sol(E) = (sol(E[x_2 := s_2]), s_2)$ with $s_2 = nu(lambda x. sol(E[x_2 := x]) and x)$. In order to find $s_2$ we will need to solve $E[x_2 := x]$, that is the system of the single fixpoint equation $x_1 feq_mu x_1 or x$ and parameterized over $x$. To do this we apply the definition again, getting $sol(E[x_2 := x]) = (sol(varempty), s_1)$ with $s_1 = mu(lambda x'. x' or x)$. At this point we have hit the base case with $sol(varempty)$, which is just $()$, while we can find $s_1$ by solving the given fixpoint equation, getting $s_1 = x$ because $x$ is the smallest value that is equal to itself when joined with $x$. We thus get $sol(E[x_2 := x]) = (x)$, and we are back to find $s_2$, whose definition can now be simplified to $nu(lambda x. x and x)$. Thus fixpoint equation can now be solved, getting $s_2 = tt$ because $tt$ is the greatest element of $bb(B)$ that also satisfies the given equation. Finally, we can get $sol(E[x_2 := s_2]) = s_2 = tt$ by substituting $s_2$ in place of $x$ in $sol(E[x_2 := x])$, and with this we get $sol(E) = (tt, tt)$.

  To recap, the steps performed were:
  - $sol(E) = (sol(E[x_2 := s_2]), s_2)$ with $s_2 = nu(lambda x. sol(E[x_2 := x]) and x)$
  - $sol(E[x_2 := x]) = (sol(varempty), s_1)$ with $s_1 = mu(lambda x'. x' or x)$
  - solving $s_1$ gives $s_1 = x$
  - solving $s_2$ gives $s_2 = nu(lambda x. x and x) = tt$
  - $sol(E) = (tt, tt)$
]

Notice that the way the solution of a system of fixpoint equations is defined depends on the order of the equations. Indeed different orders can result in different solutions.
// TODO: Connection with nested fixpoint operators?

#example("different order of equations", label: <order-equations>)[
  Consider a system of equations $E'$ containing the same fixpoint equations as $E$, but with their order swapped:
  $
    syseq(
      x_1 &feq_nu x_1 and x_2 \
      x_2 &feq_mu x_1 or x_2 \
    )
  $
  
  This time the steps needed will be the following:
  - $sol(E') = (sol(E'[x_2 := s_2]), s_2)$ with $s_2 = mu(lambda x. sol(E'[x_2 := x]) or x)$
  - $sol(E'[x_2 := x]) = (sol(varempty), s_1)$ with $s_1 = nu(lambda x'. x' and x)$
  - solving $s_1$ gives $s_1 = x$
  - solving $s_2$ gives $s_2 = mu(lambda x. x and x) = ff$
  - $sol(E') = (ff, ff)$

  Notice that $sol(E) = (tt, tt) != (ff, ff) = sol(E')$, meaning that the different order of the equations in the two systems does indeed influence the solution.
]

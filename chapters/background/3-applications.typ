#import "../../config/common.typ": *

== Applications

=== $mu$-calculus

The $mu$-calculus is a propositional modal logic extended with support for least and greatest fixpoints. It was first introduced by Dana Scott and Jaco de Bakker and later developed by Dexter Kozen in @mucalculus. It is mainly used to describe properties of (labelled) transition systems to be verified.

Consider a labelled transition system over a set of states $bb(S)$, a set of actions $Act$ and a set of transitions $-> #h(0.2em) subset.eq bb(S) times Act times bb(S)$ (usually written $s ->^a t$ to mean $(s, a, t) in #h(0.2em) ->$). Also, let $Prop$ be a set of propositions and $Var$ be a set of propositional variables. A $mu$-calculus formula for such system is defined inductively in the following way, where $a in Act$, $p in Prop$, $x in Var$ and $eta$ is either $mu$ or $nu$:

$
  phi, psi := tt | ff | p | x | phi or psi | phi and psi | diam(a) phi | boxx(a) phi | eta x. phi
$

The semantics of a formula are given by the set of states that satisfy the formula in an environment $rho : Prop union Var -> 2^bb(S)$:

#eq-columns(
  $
    sem(tt)_rho &= bb(S) \
    sem(ff)_rho &= emptyset \
    sem(p)_rho &= rho(p) \
    sem(phi or psi)_rho &= sem(phi)_rho union sem(psi)_rho \
    sem(phi and psi)_rho &= sem(phi)_rho sect sem(psi)_rho
  $,
  $
    sem(x)_rho &= rho(x) \
    sem(diam(a) phi)_rho &= { s in bb(S) | forall t. s ->^a t => t in sem(phi)_rho } \
    sem(boxx(a) phi)_rho &= { s in bb(S) | exists t. s ->^a t and t in sem(phi)_rho } \
    sem(mu x. phi)_rho &= sect.big { S subset.eq bb(S) | sem(phi)_(rho[x := S]) subset.eq S } \
    sem(nu x. phi)_rho &= union.big { S subset.eq bb(S) | S subset.eq sem(phi)_(rho[x := S]) } \
  $
)

We will thus say that a state $s$ satisfies a $mu$-calculus formula $phi$ if it is contained in its semantics, that is $s in sem(phi)_rho$, where $rho$ is initially undefined for all $x in Var$ and fixed for all $p in Prop$.

Intuitively the $mu$-calculus formulas have a similar meaning as in the common propositional logic, however it is also a modal logic thanks to the $diam(\_)$ and $boxx(\_)$ operators, requiring a formula to hold for respectively all or any state reachable by the current state through a transition with the given action. Fixpoints then allow to propagate this requirements after any number of transitions.

For convenience we will also consider a slightly more expressive variant of $mu$-calculus. We define a new set as follow, and with the following semantics:

$
  A := a | not a | tt
$
$
  sem(a) &= { a } \
  sem(not a) &= Act without { a } \
  sem(tt) &= Act
$

The definition of $mu$-calculus formulas can then be updated by replacing the constructors $[a] phi$ and $angle.l a angle.r phi$ with $[A] phi$ and $angle.l A angle.r phi$ with the following semantics:

$
  sem(diam(A) phi)_rho &= { s in bb(S) | forall t in bb(S), a in sem(A). s ->^a t => t in sem(phi)_rho } \
  sem(boxx(A) phi)_rho &= { s in bb(S) | exists t in bb(S), a in sem(A). s ->^a t and t in sem(phi)_rho }
$

For example the liveness property, or lack of deadlocks, representing the fact that from a state it is impossible to reach a state from which no transition is possible, can be expressed with the formula $nu x. boxx(tt) tt and diam(tt) x$. This can be read as requiring a state $s$ to be able to make at least one transition ($boxx(t) tt$) and that after any transition with any label from $s$ the same property should hold ($diam(tt) x$).

TODO: How to translate to system of fixpoint equations.

TODO: How to translate to logic formulas?

TODO: Mention that $mu$-calculus already admits a translation to parity games.

=== Bisimilarity

Bisimilarity @bisimilarity is a binary relation on states of a labelled transition system, where two states are in the relation if they have the same "behaviour", for some definition of behaviour. We will focus on the strong bisimilarity $bisim$, where the "behaviour" is identified with the possible transitions from a state. Bisimilarity is usually defined in terms of bisimulations, which are also binary relations on states. For the strong bisimilarity the associated bisimulations $R$ have the following requirement: 

$
  (s, t) in R 
$
$
  <=>
$
$
  forall a, s'. &s &&->^a s' &&=> exists t'. &&t &&->^a t' &&and (s', t') in R &and \
  forall a, t'. &t &&->^a t' &&=> exists s'. &&s &&->^a s' &&and (s', t') in R 
$

Bisimilarity is then defined to be biggest bisimulation, that is the bisimulation that contains all other bisimulations, or equivalently the union of all bisimulations.

TODO: Example for bisimilarity

For our purposes however there is an alternative formulation based on a greatest fixpoint:

$
  bisim #h(0.3em) = nu R. { (s, t) in R |
  &(forall a, &&s'. s &&->^a s' &&=> exists t'. &&t &&->^a t' &&and (s', t') in R)
  \ and
  &(forall a, &&t'. t &&->^a t' &&=> exists s'. &&s &&->^a s' &&and (s', t') in R)
  }
$

Most notably the set of relations is a lattice when paired with the set inclusion operator $subset$ and the given function in the fixpoint equation is monotone, so this satisfies our requirements for a system of (one) fixpoint equations we can solve.

TODO: How to translate to logic formulas

TODO: Mention the existance of a $O(M log N)$ algorithm for solving strong bisimilarity which will surely be better than solving the fixpoint equation.

=== Parity games

TODO

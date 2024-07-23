#import "../../config/common.typ": *

== Applications

=== $mu$-calculus

The $mu$-calculus is a modal logic extend with support for least and greatest fixpoints. It was first introduced by Dana Scott and Jaco de Bakker and later developed by Dexter Kozen in @mucalculus. It is mainly used to describe properties of (labelled) transition systems to be verified.

Consider a labelled transition system over a set of states $bb(S)$, a set of actions $Act$ and a set of transitions $-> #h(0.2em) subset.eq bb(S) times Act times bb(S)$ (usually written $s ->^a t$ to mean $(s, a, t) in #h(0.2em) ->$). Also, let $Prop$ be a set of propositions and $Var$ be a set of propositional variables. A $mu$-calculus formula for such system is defined inductively in the following way, where $a in Act$, $p in Prop$, $x in Var$ and $eta$ is either $mu$ or $nu$:

$
  phi, psi := tt | ff | p | x | phi or psi | phi and psi | [a] phi | angle.l a angle.r phi | eta x. phi
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
    sem([a] phi)_rho &= { s in bb(S) | forall t. s ->^a t => t in sem(phi)_rho } \
    sem(angle.l a angle.r phi)_rho &= { s in bb(S) | exists t. s ->^a t and t in sem(phi)_rho } \
    sem(mu x. phi)_rho &= sect.big { S subset.eq bb(S) | sem(phi)_(rho[x := S]) subset.eq S } \
    sem(nu x. phi)_rho &= union.big { S subset.eq bb(S) | S subset.eq sem(phi)_(rho[x := S]) } \
  $
)

// TODO: Example with liveness/safety formulas?

We will also consider a slightly more expressive variant of $mu$-calculus. We define a new set as follow, and with the following semantics:

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
  sem([A] phi)_rho &= { s in bb(S) | forall t in bb(S), a in sem(A). s ->^a t => t in sem(phi)_rho } \
  sem(angle.l A angle.r phi)_rho &= { s in bb(S) | exists t in bb(S), a in sem(A). s ->^a t and t in sem(phi)_rho }
$

// TODO: How to translate to logic formulas?

=== Bisimilarity

TODO

=== Parity games

TODO

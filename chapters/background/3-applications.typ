#import "../../config/common.typ": *
#import "@preview/cetz:0.2.2": canvas, draw

== Applications

In this section we discus two classical verification problems, model checking behavioural properties expressed in the $mu$-calculus and checking behavioral equivalece formalized as bisimilarity. We show that both can be seen as istances
of the solution of a system of fixpoint equations.

=== $mu$-calculus <mucalculus-application>

The $mu$-calculus is a propositional modal logic extended with support for least and greatest fixpoints. It was first introduced by Dana Scott and Jaco de Bakker and later developed by Dexter Kozen in @mucalculus. Its main use is to help describing properties of (labelled) transition systems to be verified.

Consider a labelled transition system over a set of states $bb(S)$, a set of actions $Act$ and a set of transitions $-> #h(0.2em) subset.eq bb(S) times Act times bb(S)$ (usually written $s ->^a t$ to mean $(s, a, t) in #h(0.2em) ->$). Also, let $Prop$ be a set of propositions and $Var$ be a set of propositional variables. A $mu$-calculus formula for such system is defined inductively in the following way, where $a in Act$, $p in Prop$, $x in Var$ and $eta$ is either $mu$ or $nu$:
// TODO: Esempi

$
  phi, psi := tt | ff | p | x | phi or psi | phi and psi | boxx(a) phi | diam(a) phi | eta x. phi
$

The semantics of a formula are given by the set of states that satisfy the formula in an environment. Given $rho : Prop union Var -> 2^bb(S)$, we define:

#eq-columns(
  $
    sem(tt)_rho &= bb(S) \
    sem(ff)_rho &= varempty \
    sem(p)_rho &= rho(p) \
    sem(phi or psi)_rho &= sem(phi)_rho union sem(psi)_rho \
    sem(phi and psi)_rho &= sem(phi)_rho sect sem(psi)_rho
  $,
  $
    sem(x)_rho &= rho(x) \
    sem(boxx(a) phi)_rho &= { s in bb(S) | forall t. s ->^a t => t in sem(phi)_rho } \
    sem(diam(a) phi)_rho &= { s in bb(S) | exists t. s ->^a t and t in sem(phi)_rho } \
    sem(mu x. phi)_rho &= sect.big { S subset.eq bb(S) | sem(phi)_(rho[x := S]) subset.eq S } \
    sem(nu x. phi)_rho &= union.big { S subset.eq bb(S) | S subset.eq sem(phi)_(rho[x := S]) } \
  $
)

We will thus say that a state $s$ satisfies a $mu$-calculus formula $phi$ if it is contained in its semantics, that is $s in sem(phi)_rho_0$, where $rho_0$ is initially irrelevant for all $x in Var$ and with some fixed value for all $p in Prop$.

Intuitively $tt$, $ff$, $p$, $x$, $phi or psi$ and $phi and psi$ formulas enriches the common propositional logic with the modal operators $boxx(\_)$ and $diam(\_)$, which require a formula to hold for respectively all or any state reachable by the current state through a transition with the given action. On top of this fixpoints then allow to express recursive properties, for example to propagate some requirements across any number of transitions.

// TODO: Rewrite with A subset of Act?
For convenience we will also consider a slightly more expressive variant of $mu$-calculus. We define a new set as follow, and with the following semantics:

$
  A := a | not a | tt
$
$
  sem(a) &= { a } \
  sem(not a) &= Act without { a } \
  sem(tt) &= Act
$

This extension makes it simplier to require a formula to hold for any successor, or any successor with a transition with a label different from the given one. This extension does not actually give $mu$-calculus more expressiveness, but it allows us to specify some properties in a easier way.

The definition of $mu$-calculus formulas can then be updated by replacing the constructors $[a] phi$ and $angle.l a angle.r phi$ with $[A] phi$ and $angle.l A angle.r phi$ with the following semantics:

$
  sem(boxx(A) phi)_rho &= { s in bb(S) | forall &&t in bb(S), a in sem(A). s ->^a t => t in sem(phi)_rho } \
  sem(diam(A) phi)_rho &= { s in bb(S) | exists &&t in bb(S), a in sem(A). s ->^a t and t in sem(phi)_rho }
$

For example the liveness property, or lack of deadlocks, which expresses the fact that all reachable states can make at least one transition, can be expressed with the formula $nu x. diam(tt) tt and boxx(tt) x$. This can be read as requiring a state $s$ to be able to make at least one transition, that is it satisfies $diam(tt) tt$, and that after one transition the same property should hold, that is it satisfies $boxx(tt) x$. Intuitively the fixpoint is extending the first requirement to any state reachable after a number of transitions.

It is possible to translate $mu$-calculus formulas into systems of fixpoint equations over $2^bb(S)$, the powerset lattice of its states. Such system can be obtained by extracting each fixpoint subformula into its own equation and replacing it with its variable, assuming that no variable is used in multiple fixpoints. Since the order of equations matter, outer fixpoints must appear later in the system of equations. It can be shown that each function in the system is monotone, and so it always admits a solution.

For example the formula $mu x. diam(tt) x or (nu y. boxx(a) y and x)$ would be translated into the following system, where for simplicity we used formulas instead of their semantics:

$
  syseq(
    y &feq_nu boxx(a) y and x \
    x &feq_mu diam(tt) x or y \
  )
$

=== Bisimilarity <bisimilarity-application>

Bisimilarity @bisimilarity is a binary relation on states of a labelled transition system, where two states are in the relation if they are indistuinguishable by only looking at some kind of behaviour. We will focus on the strong bisimilarity $bisim$, where such behaviour is identified with the possible transitions from a state. Bisimilarity is usually defined in terms of bisimulations, which are also binary relations on states. For the strong bisimilarity the associated bisimulations $R$ have the following requirement: 

#definition("bisimulation")[
  Let $(bb(S), Act, ->)$ be a labelled transition system. A relation $R subset.eq bb(S) times bb(S)$ is a bisimulation if for all $s, t in bb(S)$ the following holds:
  $
    (s, t) in R 

    #h(2em)
    <=>
    #h(2em)
    
    #block($
      forall a, s'. &s &&->^a s' &&=> exists t'. &&t &&->^a t' &&and (s', t') in R &
      \
      #hide($and$)#place(dx: 5.7em, dy: -0.4em, sym.and)
      \
      forall a, t'. &t &&->^a t' &&=> exists s'. &&s &&->^a s' &&and (s', t') in R
    $)
  $
]

Bisimilarity is then defined to be the largest bisimulation, that is the bisimulation that contains all other bisimulations, or equivalently the union of all bisimulations.

#let bisimilarity_example = canvas({
  import draw: *

  set-style(content: (padding: .2), stroke: black)

  let node(pos, name, label) = {
    circle(pos, name: name, radius: 1em)
    content(pos, label)
  }
  let edge(ni, ai, nf, af, a, l, d) = {
    let pi = (name: ni, anchor: ai)
    let pf = (name: nf, anchor: af)
    let bname = ni + "-" + nf
    bezier(pi, pf, (pi, 50%, a, pf), name: bname, fill: none, mark: (end: ">"))
    content(bname + ".ctrl-0", l, anchor: d)
  }

  node((1, 0), "v0", $v_0$)
  node((0, -1.5), "v1", $v_1$)
  node((2, -1.5), "v2", $v_2$)
  node((1, -3), "v3", $v_3$)
  edge("v0", 200deg, "v1", 80deg, -20deg, $a$, "east")
  edge("v0", -20deg, "v2", 100deg, 20deg, $a$, "west")
  edge("v1", -80deg, "v3", 160deg, -20deg, $b$, "east")
  edge("v2", -100deg, "v3", 20deg, 20deg, $b$, "west")

  node((6, 0), "u0", $u_0$)
  node((6, -1.5), "u1", $u_1$)
  node((6, -3), "u2", $u_2$)
  edge("u0", -90deg, "u1", 90deg, 0deg, $a$, "west")
  edge("u1", -90deg, "u2", 90deg, 0deg, $b$, "west")
})

#figure(
  bisimilarity_example,
  caption: [Example of a strong bisimilarity problem],
) <bisimilarity-example>

Consider for example the two given labelled transition systems given above. They are obviously different, but by only looking at the possible transitions it is impossible to distinguish $v_0$ from $u_0$, hence they are bisimilar. It is instead possible to distinguish $v_1$ from $u_0$, because the former can perform one transition with action $b$ while the latter can only perform a transition with action $a$, and thus they are not bisimilar.

For our purposes however there is an alternative formulation based on a greatest fixpoint:
// TODO: Go through an operator F: 2^(bb(S) times bb(S)) -> 2^(bb(S) times bb(S))

$
  bisim #h(0.3em) = nu R. { (s, t) in R |
  &(forall a, &&s'. s &&->^a s' &&=> exists t'. &&t &&->^a t' &&and (s', t') in R)
  \ and
  &(forall a, &&t'. t &&->^a t' &&=> exists s'. &&s &&->^a s' &&and (s', t') in R)
  }
$

This is a single fixpoint equation over $2^(bb(S) times bb(S))$, the powerset lattice of binary relations of states, and it can be shown the associated function is monotone.

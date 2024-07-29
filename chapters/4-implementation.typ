#import "../config/common.typ": *

= Implementation and performance considerations

The final goal of this thesis was a concrete implementation of the algorithms explained until now, which ultimately was a rewrite and expansion of the work done in LCSFE @flori to use a different and possibly better algorithm for solving the generated parity game. The final implementation is available in the repository #underline(link("https://github.com/SkiFire13/master-thesis-code"))

In this section we will explain our design choices, what was actually implemented, and we will give a performance comparison with some existing tools.

// TODO: Link to implementation

== Technologies used

// TODO: Cite Rust
Just like LCSFE, our implementation is written in Rust, a modern systems programming language, focused on performance and correctness and whose goal is to rival languages like C and C++ while offering memory safety. Just like C and C++, Rust mainly follows the imperative paradigm, allowing mutations, loops and general side effects, but it also includes lot of functional programming related features, like algebraic data structures and most notably _enums_, pattern matching, which allows to exhaustively inspect those enums, and closures, which are anonymous function that can capture their outer environment, although with some limitations due to how the memory management works. Rust is also immutability by default, which has become quite popular recently and helps avoid some classes of logic errors. Among other features there are _traits_, which work similarly to type classes in Haskell and fill the same usecases as interfaces in popular OOP languages like Java. It should also be mentioned that in Rust programs are organized in crates, which make up the unit of compilation, and modules, which are a hierarchical division internal to a crate and help organize code and avoid name clashes.

The most interesting features however are its _ownership_ system and its borrow checker, which allow the compiler to guarantee memory safety without a garbage collection or other kind of runtime support. The ownership system enforces that every value has exactly one _owner_, which is responsible for freeing up its resources, making classes of issues like use-after-free impossible, and others like memory leaking much more difficult to hit. The borrow checker instead rules how borrows can be created and used. Every variable can be borrowed, creating either a shared reference or an exclusive references, which are pointers with a special meaning for the compiler. The borrow checker ensures that at any point in time there can be either multiple shared references or one exclusive reference pointing to a variable, but not both. Coupled with the fact that only exclusive references allow mutations, this system guarantees that references always point to valid data.

// TODO: Cite data oriented programming
The borrowing rules however can become an obstacle when writing programs that perform lot of mutations, especially for programmers used to other imperative languages. It has been found however that data oriented designs in practice work pretty well with the borrow checker, due to the ability to replace pointers with indexes and thus restricting the places where borrows need to be created. This paradigm also helps creating cache efficient programs, which can often be faster. For this reason we tried to implement out algorithm with a data oriented design, which was mainly done by associating an auto-incrementing index to each vertex. Then informations associated with vertices, like their successors or remaining moves, was each stored in its own array indexed by the same index on vertices.

== Structure of the implementation

The implementation was splitted in multiple crates, just like in the original LCSFE implementation, however compared to it it was simplified a bit, with just one main _solver_ crate implementing the solving algorithm and multiple dependent crates, some that translate specific problems into systems of fixpoint equations with logic formulas ready to be solved by the solver crate, and others that offer a CLI interface for testing such functionalities. The solver crate was then splitted into three main modules:

- _symbolic_, which defines the structures for systems of fixpoint equation, logic formulas, symbolic moves and other relevant methods for manipulating them;
- _strategy_, which implements the strategy iteration algorithm;
- _local_, which implements the local algorithm and the expansion scheme, along with the improvement we made to them.

The dependent crates are:

- _parity_, which implements the parsing and translation from parity games to a system of fixpoint equations, which we see in section @parity-implementation, and a binary crate for the associated CLI;
- _mucalc_, which implements the parsing of labelled transition system files from the AUT format (also called Aldebaran), the parsing of a subset of $mu$-calculus formulas and the translation from them to a system of fixpoint equations, along with a binary crate for the associated CLI;
// TODO: Cite paper of AUT format (?)
- _bisimilarity_, which implements the translation from a bisimilarity problem between two states of two different labelled transition systems to a system of one fixpoint equation, along with a bianry crate for the associated CLI. 

== Testing with parity games <parity-implementation>

It is known that parity games can also be translated to systems of fixpoint equations, and we used this fact to generate simple problems for testing our implementation.

In particular, given a parity game $G = (V_0, V_1, E, p)$ we can define a system of fixpoint equations on the lattice ${w_1, w_0}$, with $subset.sq$ such that $w_1 subset.sq w_0$, essentially making $w_1$ the bottom element and $w_0$ the top element. Each $w_i$ represents the fact that player $i$ wins on a given vertex. The basis will be ${w_0}$, since $w_1 = join varempty$ and $w_0 = join { w_0 }$. Then for each vertex $v in V_0 union V_1$ a variable $x_v$ will defined along with one of these equations:

$
  x_v feq_eta union.sq.big_(u in v E) x_u & "if " v in V_0 \
  x_v feq_eta sect.sq.big_(u in v E) x_u & "if " v in V_1 
$

Intuitively, a vertex in $V_0$ is winning for player 0 if any of its successors is also winning for them because they can choose to move to that successor, while a vertex in $V_1$ is winning for player 0 if all its successors are winning for them because otherwise player 1 will choose to move to any successor that is not winning for player 0.

The priority of vertices must however also be taken into account in order to determine the winner of infinite plays. To do this the kind of fixpoints and the order of equations in the systems is used, in particular it is set $eta = nu$ if $p(v)$ is even and $eta = mu$ if $p(v)$ is odd. The equations then need to be sorted such that the equation for $x_v$ must appear before the one for $x_u$ if $p(v) < p(u)$. (TODO: Cite paper where this is proven to be correct?)

These functions can be trivially converted to logic formulas. Notice that the atom $(w_0, i)$, where $i$ is the index of the equation with variable $x_u$, is true if and only if the solution for $x_u$ is $w_0$, otherwise if the atom is false then the solution is $w_1$. As such the equations of the system can be converted to logic formulas by replacing each variable $x_u$ with the atom $(w_0, i)$, where $i$ is the index of variable the $x_u$, each $join$ with $or$ and each $meet$ with $and$.

The _parity_ crate implements this conversion from parity games to systems of fixpoint equations and then logic formulas, along with a parser for parity games specified in the pgsolver @pgsolver format, according to the following EBNF grammar:

#[
  #show "<": sym.angle.l
  #show ">": sym.angle.r

  #let s = h(0.5em)

  #let paritygame = mathstr("parity_game")
  #let nodespec = mathstr("node_spec")
  #let identifier = mathstr("identifier")
  #let priority = mathstr("priority")
  #let owner = mathstr("owner")
  #let successors = mathstr("successors")
  #let name = mathstr("name")

  $
    <paritygame> &::= [sans("parity") < identifier > #s sans(";")] #s <nodespec>^+ \
    <nodespec> &::= <identifier> #s <priority> #s <owner> #s <successors> #s [<name>] #s sans(";") \
    <identifier> &::= bb(N) \
    <priority> &::= bb(N) \
    <owner> &::= sans("0") | sans("1") \
    <successors> &::= <identifier> #s (, #s <identifier>)^* \
    <name> &::= sans("\"") #s ("any ASCII string not containing '\"'") #s sans("\"") \
  $
]

For simplicity we didn't implement the full grammar specification, but only the useful parts for testing.

TODO: example of parity game converted to system of fixpoint equations?

We then used the parity game instances included in the Oink @oink collection of parity game solvers to test our implementation.

== Testing with $mu$-calculus

As mentioned in @mucalculus-application and @mucalculus-translation, $mu$-calculus formulas can be translated to systems of fixpoint equations and then to logic formulas. We implemented this in the _mucalc_ crate, which does this after parsing a labeled transition system and a $mu$-calculus formula from two given files.

The labelled transition system is expected to be in the AUT (Aldebaran) format, according to the following EBNF grammar, based on @aut_spec:

#[
  #show "<": sym.angle.l
  #show ">": sym.angle.r

  #let s = h(0.5em)

  #let aut = mathstr("aut")
  #let header = mathstr("header")
  #let initialstate = mathstr("initial-state")
  #let transitionscount = mathstr("transitions-count")
  #let statescount = mathstr("states-count")
  #let transition = mathstr("transition")
  #let fromstate = mathstr("from-state")
  #let label = mathstr("label")
  #let unquotedlabel = mathstr("unquoted-label")
  #let quotedlabel = mathstr("quoted-label")
  #let tostate = mathstr("to-state")

  $
    <aut> &::= <header> #s <transition>^* \
    <header> &::= sans("des") #s sans("(") #s <initialstate> #s sans(",") #s <transitionscount> #s sans(",") #s <statescount> sans(")" #s) \
    <initialstate> &::= bb(N) \
    <transitionscount> &::= bb(N) \
    <statescount> &::= bb(N) \
    <transition> &::= sans("(") #s <fromstate> #s sans(",") #s <label> #s sans(",") #s <tostate> #s sans(")") \
    <fromstate> &::= bb(N) \
    <label> &::= <unquotedlabel> | <quotedlabel> \
    <unquotedlabel> &::= ("any character except \"" #h(0.3em)) #s ("any character except ," #h(0.3em))^* \
    <quotedlabel> &::= sans("\"") #s ("any character except \"" #h(0.3em))^* #s sans("\"") \
    <tostate> &::= bb(N) \
  $
]

The grammar consists of a header containing the literal "des" followed by the initial state number, the number of transitions and the number of states. Following that are all the transitions, encoded as a triple with the starting state, the label, which can be quoted or not, and the ending state. Differently from the specification at @aut_spec, we have preferred a slightly different definition for the quoted and unquoted labels to simplify the implementation. We have not observed inputs for which out definition makes a difference.

The expect $mu$-calculus formula is expected to be of the more expressive variant described in @mucalculus-application, according to the following EBNF grammar:

#[
  #show "<": sym.angle.l
  #show ">": sym.angle.r

  #let s = h(0.5em)

  #let expr = mathstr("expr")
  #let fixexpr = mathstr("fix-expr")
  #let var = mathstr("var")
  #let orexpr = mathstr("or-expr")
  #let andexpr = mathstr("and-expr")
  #let modalexpr = mathstr("modal-expr")
  #let action = mathstr("action")
  #let label = mathstr("label")
  #let atom = mathstr("atom")

  $
    <expr> &::= <fixexpr> | <orexpr> \
    <fixexpr> &::= (sans("mu") | sans("nu")) #s <var> #s sans(".") #s <orexpr> \
    <var> &::= ("any identifier") \
    <orexpr> &::= <andexpr> #s (#s sans("||") #s <andexpr> #s)^* \
    <andexpr> &::= <modalexpr> #s (#s sans("&&") #s <modalexpr> #s)^* \
    <modalexpr> &::= (sans("＜") #s action #s sans("＞") #s atom)
      | ( #s sans("[") #s action #s sans("]") #s atom )
      | atom \
    <action> &::= label | sans("not") #s label | sans("true") \
    <label> &::= ("any character except ＞ and ]" #h(0.3em)) \
    <atom> &::= sans("true") | sans("false") | <var> | sans("(") #s <expr> #s sans(")") 
  $
]

This follows the formal definition of a $mu$-calculus formula given previously, with the main changes being the replacement of mathematical symbols in favour of ASCII characters and a more explicit definition of the precedence rules.

The two grammars for labelled transition systems and $mu$-calculus formulas have been chosen to be compatible with the ones used in LCSFE, in order to simplify a comparison between the two. However they have also been extended in order to allow for quoted labels in the labelled transition system grammar, which appeared in some instances used for testing, and more convenient precedence rules for the $mu$-calculus grammar, which helped when writing some more complex formulas.

// TODO: mucalc Gossips vs Flori vs mCRL2 (bad case deadlock and better case ??)
// TODO: mucalc Evaluation on VLTS benchmarks (bad cases and good cases)

// TODO: Generate random FIFO/LIFO using CADP?
// TODO: Comparisons with and without improvements?

== Testing with bisimilarity
// TODO: Testing bisimilarity

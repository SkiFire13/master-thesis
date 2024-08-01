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
    <action> &::= sans("true") | label | sans("not") #s label \
    <label> &::= ("any character except ＞ and ]" #h(0.3em)) \
    <atom> &::= sans("true") | sans("false") | <var> | sans("(") #s <expr> #s sans(")") 
  $
]

This follows the formal definition of a $mu$-calculus formula given previously, with the main changes being the replacement of mathematical symbols in favour of ASCII characters and a more explicit definition of the precedence rules.

The two grammars for labelled transition systems and $mu$-calculus formulas have been chosen to be compatible with the ones used in LCSFE, in order to simplify a comparison between the two. However they have also been extended in order to allow for quoted labels in the labelled transition system grammar, which appeared in some instances used for testing, and more convenient precedence rules for the $mu$-calculus grammar, which helped when writing some more complex formulas.

=== Performance comparison

We compared the performance with LCSFE and mCRL2 on the mCRL2 examples used originally in @flori. All the tests were performed on a computer equipped with a AMD Ryzen 3700x and 32GB of DDR4 RAM running Windows 10. LCSFE and our implementation were compiled using Rust's release profile.

We started with the "bridge referee" example from mCRL2, a labelled transition system with 102 states and 177 transitions, checking the formula $mu x. diam(#h(0em)"report"(17)) #h(0.3em) tt or diam(tt) #h(0.3em) x$, corresponding to the fact that from the initial state the system can reach a state where a transition with label "report(17)" can be performed. Using mCRL2's suggested workflow we first converted the mCRL2 specification into its internal lps format using the `mcrl22lps` utility:

```cmd
> mcrl22lps bridge-referee.mcrl2 bridge.lps --timings
```
```
- tool: mcrl22lps
  timing:
    total: 0.024
```

Then, we bundled together the lps file and a file holding the formula specified above into a pbes file, another internal format, using the `lps2pbes` utility.

```cmd
> lps2pbes bridge.lps --formula=bridge_report_17.mcf \
  bridge_report_17.pbes --timings
```
```
- tool: lps2pbes
  timing:
    total: 0.016
```

Finally, the `pbes2bool` was used to convert the pbes file into a boolean parity game and solve it. It should be noted that $mu$-calculus also admits an ad-hoc translation to parity games, which we would expect to be better than our generic approach.

```cmd
> pbes2bool bridge_report_17.pbes -rjittyc --timings
```
```
true
- tool: pbes2bool
  timing:
    instantiation: 0.009495
    solving: 0.000028
    total: 0.038349
```

We then verified the same formula with LCSFE and our implementation. We used mCRL2 again to convert the mCRL2 machine specification to a labelled transition system in AUT format we can use. To do this we reused the lps file previously generated to produce a lts file using the `lps2lts` utility:

```cmd
> lps2lts bridge.lps bridge.lts -rjittyc --timings
```
```
- tool: lps2lts
  timing:
    total: 0.035608
```

The lts file was then converted to an AUT file using the `ltsconvert` utility, which converts between different labelled transition systems formats:

```cmd
> ltsconvert bridge.lts bridge.aut --timings
```
```
- tool: ltsconvert
  timing:
    reachability check: 0.000
    total: 0.002
```

Finally we verified the formula using LCSFE and our implementation

```cmd
> lcsfe-cli mu-ald bridge.aut bridge_report_17.mcf 0
```
```
Preprocessing took: 0.0004837 sec.
Solving the verification task took: 0.0000129 sec.
Result: The property is satisfied from state 0
```

```cmd
> mucalc bridge.aut bridge_report_17.mcf
```
```
Preprocessing took 432.1µs
Solve took 1.1076ms
The formula is satisfied
```

In this very small example we can see that our implementation is slightly slower. However it should be noted that it is also doing slightly more work by bridging the symbolic formulation and the strategy iteration solver, thus masking any potential difference in complexity.

We then tested the second formula that was used in @flori, which uses the bigger "gossip" labelled transition system, also an example from mCRL2, with 9152 states and 183041 transitions. The formula tested was $nu x. diam(tt) tt and boxx(tt) x$, which represents the lack of deadlocks. It should be noted that formulas checking for absence of deadlock that are satisfied, like this one, are a worst case for local algorithms because they require visiting the whole graph, thus negating the advantage of local algorithms to visit only the states that are relevant.

Just like before we first checked it using mCRL2:

```cmd
> mcrl22lps gossip.mcrl2 gossip.lps --timings
```
```
- tool: mcrl22lps
  timing:
    total: 0.043529
```

```cmd
> lps2pbes gossip.lps --formula=gossip1_deadlock_liveness.mcf \
  gossip1.pbes --timings
```
```
- tool: lps2pbes
  timing:
    total: 0.019922
```

```cmd
> pbes2bool gossip1.pbes -rjittyc --timings
```
```
true
- tool: pbes2bool
  timing:
    instantiation: 1.395733
    solving: 0.001688
    total: 1.422398
```

Which confirms the formula to be valid. Then as before we used mCRL2 to convert it to the AUT format and checked it again using LCSFE and our implementation. It should be noted that for LCSFE we had to rise the default stack space since the recursive nature of the solver lead it to a stack overflow.

```cmd
> lps2lts gossip.lps gossip.lts -rjittyc --timings
```
```
- tool: lps2lts
  timing:
    total: 1.507845
```

```cmd
> ltsconvert gossip.lts gossip.aut --timings
```
```
- tool: ltsconvert
  timing:
    reachability check: 0.004988
    total: 0.269247
```

```cmd
> lcsfe-cli mu-ald gossip.aut gossip1_deadlock_liveness.mcf 0
```
```
Preprocessing took: 0.1968049 sec.
Solving the verification task took: 5.6878138 sec.
Result: The property is satisfied from state 0
```

```cmd
> mucalc gossip.aut gossip1_deadlock_liveness.mcf
```
```
Preprocessing took 38.8635ms
Solve took 164.6531ms
The formula is satisfied
```

Our implementation is an order of magnitude faster than LCSFE, confirming that the better parity game solving algorithm does make a difference, to the point where the bottleneck becomes the generation of the AUT file. Compared with mCRL2 our implementation overall takes a similar amount of time, most of which is spent doing conversions with mCRL2. Overall however the pure mCRL2 approach is slightly faster, probably due to the costs of the intermediate conversions to produce the AUT file or the overhead of using a local algorithm in a case where all states must be explored regardless.

We also ran our solver on some of the instances in the VLTS benchmark suite to understand the limitations and the strengths of our implementation. For each chosen instance we verified the $mu$-calculus formulas $nu x. diam(tt) tt and boxx(tt) x$, which checks for absence of deadlocks, and $mu x. diam(tt) x or (mu y. diam(#h(0em)"tau"#h(0em)) y)$, which checks for the presence of livelocks, which are of only tau transitions. This time we considered the total time including preprocessing, which eventually becomes negligible. For each instance we ran the solver 5 times, ignored the slowest and quickest ones and reported a mean of the remaining 3.

#[
  #set text(size: 10pt)
  #figure(
    table(
      columns: (auto, 4.5em, 4.5em, 4.5em, auto, 4.5em, auto),
      align: horizon,
      inset: (x: 0.3em),
      table.header([*Name*], [*States count*], [*Trans. count*], [*Deadlocks?*], [*Deadlock solve time*], [*Livelocks?*], [*Livelock solve time*]),
      `cwi_1_2`, [1952], [2387], [no], [8.74 ms], [no], [13.4 ms],
      `vasy_0_1`, [289], [1224], [no], [4.93 ms], [no], [6.06 ms],
      `vasy_52_318`, [52268], [318126], [no], [443 s], [yes], [34.9 s],
      `vasy_69_520`, [69754], [520633], [yes], [122 ms], [no], [6.09 s],
      `vasy_720_390`, [720247], [390999], [yes], [82 ms], [no], [3.40 s],
    ),
    caption: [VLTS benchmark results]
  )
]

The various labelled transition systems have different sizes, and some have deadlocks and livelocks while others do not, which greately influences the results and makes the various results not directly comparable to one another. We can for example see that checking for the absense of deadlocks when they are not present quickly becomes very slow, like in `vasy_52_318` where in particular we observed that even single iterations of the strategy iteration algorithm become quite slow. Checking for livelocks instead appears to be generally slower when the answer is negative, because in those cases it doesn't suffice to find the cycle with tau transitions but instead all the graph needs to be considered.

The `vasy_720_390` instance is also interesting because it is not connected, with only 87740 states which are actually reachable from the initial one. This is a favourable case for local algorithms, and in fact the time required to verify the formulas is proportional to the number of actually reachable states rather than the full amount.

// TODO: diam and boxx are wrong (inverted?). Also re-check the livelock formula

TODO: Generate random FIFO/LIFO using CADP and gather measurements on them?

TODO: Comparisons with and without improvements?

== Testing with bisimilarity
// TODO: Testing bisimilarity

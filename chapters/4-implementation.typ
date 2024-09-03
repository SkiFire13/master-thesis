#import "../config/common.typ": *
#import "@preview/cetz:0.2.2": canvas, draw

= Implementation <section-implementation>

The final goal of this thesis was a concrete implementation of the algorithms explained in the previous sections. The implementation partly relies on the work done in LCSFE @flori which, as mentioned in the introduction, was based on a different algorithm for parity games. The final implementation is available in the repository #underline(link("https://github.com/SkiFire13/master-thesis-code"))

In this section we will explain our design choices, what was actually implemented, and we will present a performance comparison with some existing tools.

== Technologies used

Just like LCSFE, our implementation is written in Rust @rust, a modern systems programming language, focused on performance and correctness and whose goal is to rival languages like C and C++ while offering memory safety. Just like C and C++, Rust mainly follows the imperative paradigm, allowing mutations, loops and general side effects, but it also includes lot of functional programming related features, like algebraic data structures and most notably _enums_, pattern matching, which allows to exhaustively inspect those enums, and _closures_, which are anonymous function that can capture their outer environment, although with some limitations due to how the memory management works. Among other features there are _traits_, which work similarly to type classes in Haskell and fill the same use cases as interfaces in popular OOP languages like Java. It should also be mentioned that Rust programs are organized in _crates_, which make up the unit of compilation, and _modules_, which are a hierarchical division internal to a crate and help organize code and avoid name clashes.

The most interesting features however are its _ownership_ system and its borrow checker, which allow the compiler to guarantee memory safety without a garbage collection or other kind of runtime support. The ownership system enforces that every value has exactly one _owner_, which is responsible for freeing up its resources, making classes of issues like use-after-free impossible, and others like memory leaking much more difficult to hit. The borrow checker instead rules how borrows can be created and used. Every variable can be borrowed, creating either a shared reference or an exclusive references, which are pointers with a special meaning for the compiler. The borrow checker ensures that at any point in time there can be either multiple shared references or one exclusive reference pointing to a variable, but not both. Coupled with the fact that only exclusive references allow mutations, this system guarantees that references always point to valid data.

// TODO: Cite data oriented programming
The borrowing rules however can become an obstacle when writing programs that perform lot of mutations, especially for programmers used to other imperative languages. It has been found however that data oriented designs in practice work pretty well with the borrow checker, due to the ability to replace pointers with indexes and thus restricting the places where borrows need to be created. This paradigm also helps creating cache efficient programs, which can often be faster. For this reason we tried to implement out algorithm with a data oriented design, which was mainly done by associating an auto-incrementing index to each vertex. Then informations associated with vertices, like their successors or remaining moves, was each stored in its own array indexed by the same index on vertices.

== Structure of the implementation

The implementation was split in multiple crates, just like in the original LCSFE implementation. It consists of one main _solver_ crate implementing the solving algorithm and multiple dependent crates, that translate specific problems into systems of fixpoint equations with logic formulas ready to be solved by the solver crate and offer a CLI interface for testing such functionalities. 

#figure(
  canvas({
    import draw: *

    let edge(pi, pf, a) = {
      bezier(pi, pf, (pi, 50%, a, pf), fill: none, stroke: black, mark: (end: ">"))
    }
    let inner_edge(pi, pf, a) = {
      bezier(pi, pf, (pi, 50%, a, pf), fill: none, stroke: black, mark: (start: ">", end: ">"))
    }

    content((-4, 4), box(stroke: black, inset: 0.6em)[_parity_])
    content((0, 4), box(stroke: black, inset: 0.6em)[_mucalc_])
    content((4, 4), box(stroke: black, inset: 0.6em)[_bisimilarity_])
    content((1.5, 2), box(stroke: black, inset: 0.6em)[_aut_])

    content((-1.8, 0), [_solver_])
    content((0, 0), box(stroke: black, inset: 0.6em)[_local_])
    content((-1.5, -2), box(stroke: black, inset: 0.6em)[_strategy_])
    content((1.5, -2), box(stroke: black, inset: 0.6em)[_symbolic_])
    rect((-2.5, 0.5), (2.6, -2.5), name: "s")

    edge((-4, 3.63), (-1.3, 0.5), 0deg)
    edge((0, 3.63), (0, 0.5), 0deg)
    edge((4, 3.63), (1.3, 0.5), 0deg)

    edge((0.3, 3.63), (1.2, 2.37), 0deg)
    edge((3.7, 3.63), (1.8, 2.37), 0deg)
    
    inner_edge((-0.2, -0.37), (-1.5, -1.63), 0deg)
    inner_edge((0.2, -0.37), (1.5, -1.63), 0deg)
  }),
  caption: [Crates tree of the implementation]
)

The crates involved are the following:

- _parity_, which implements the parsing and translation from parity games to a system of fixpoint equations, which we saw in section @parity-implementation, and a binary crate for the associated CLI;
- _aut_, which implements the parsing of labelled transition system files from the AUT format (also called Aldebaran) and is consumed by both the _mucalc_ and _bisimilarity_ crates;
- _mucalc_, which implements the parsing of a subset of $mu$-calculus formulas, followed by their translation to a system of fixpoint equations and logic formulas as shown in @mucalculus-application[Sections] and @mucalculus-translation[], and along with a binary crate for the associated CLI;
- _bisimilarity_, which implements the translation from a bisimilarity problem between two states of two different labelled transition systems to a system of one fixpoint equation and then logic formulas as shown in @bisimilarity-application[Sections] and @bisimilarity-translation[], along with a binary crate for the associated CLI.

The _solver_ crate is also internally split into three main modules implementing the major pieces of functionality:

- _symbolic_, which defines the structures for systems of fixpoint equation and logic formulas, and more importantly implements formula iterators their simplification;
- _strategy_, which implements the strategy iteration algorithm;
- _local_, which implements the local algorithm and the expansion scheme, along with the improvement we made to them, connecting to the _symbolic_ module to generate new moves when necessary and to the _strategy_ module to perform the valuation and improvement steps.


== Testing with parity games <parity-implementation>

As mentioned in @parity-translation parity games can be translated to systems of fixpoint equations, and we used this fact to generate simple problems for testing our implementation.

The _parity_ crate implements this conversion from parity games to systems of fixpoint equations and then logic formulas, along with a parser for parity games specified in the pgsolver @pgsolver format, according to the following grammar:

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

For example the parity game shown in @parity-example would be specified in the following way:

```
parity 5
0 0 0 1,2;
1 2 1 0;
2 3 1 1,3;
3 5 0 4;
4 4 0 2,3;
```

The format consists of a header containing the identifier $sans("parity")$ followed by a number indicating how many vertices will be specified, which can be used to speed up the parsing of the file. Then each of the following lines specifies a vertex with, in order, its identifier, priority, controlling player, edges and optionally a name. For the sake of simplicity we assumed the names to never be present, since they are not required for solving the game and were not present in the games we exploited for our testing activity.

We used the parity game instances included in the Oink @oink collection of parity game solvers to test our implementation. These tests are pretty small, reaching a maximum of 24 vertices and 90 edges, but they include lot of tricky cases which help getting empiric evidence of the correctness of our implementation.

== Testing with $mu$-calculus

As mentioned in @mucalculus-application[Sections] and @mucalculus-translation[], $mu$-calculus formulas can be translated to systems of fixpoint equations and then to logic formulas. We implemented this in the _mucalc_ crate, which performs this translation after parsing a labeled transition system and a $mu$-calculus formula from two given files.

The labelled transition system is expected to be in the AUT (Aldebaran) format, according to the following grammar, which based on the one given in @aut_spec:

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

The grammar consists of a header containing the literal "des" followed by the initial state number, the number of transitions and the number of states. After that, are all the transitions, encoded as a triple $(s, l a b e l, t)$, where the first and last components $s$ and $t$ are the source and target state of the transition, while the second component is the label, which can be quoted or not. For the sake of simplicity we have diverged from the specification at @aut_spec by considering labels as either a sequence of characters until the first comma or as sequence of characters delimited by quotes. In particular we have ignored character escaping and any restrictions on which characters are allowed to be used.

The given grammar for a $mu$-calculus formula mostly follows the definition previously given in @mucalculus-application:

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
    <modalexpr> &::= (sans("＜") #s <action> #s sans("＞") #s <atom>)
      | ( #s sans("[") #s <action> #s sans("]") #s <atom> )
      | atom \
    <action> &::= sans("true") | <label> | sans("!") #s <label> \
    <label> &::= ("any character except ＞ and ]" #h(0.3em)) \
    <atom> &::= sans("true") | sans("false") | <var> | sans("(") #s <expr> #s sans(")") 
  $
]

Compared to the definition given in @mucalculus-application we have omitted support for arbitrary propositions. Arbitrary subsets of labels are also not supported, but are instead limited to singleton sets containing a label, their complement, signaled by a $sans(!)$ character preceding a label, or the set of all labels, represented by the $sans("true")$ action. From now on we will use $mu$-calculus formulas that follow this syntax. Several mathematical symbols have also been replaced with similar ASCII characters, and precedence rules have been encoded in the grammar.

The two grammars for labelled transition systems and $mu$-calculus formulas have been chosen to be mostly compatible with the ones used in LCSFE, from which their limitations also come from, in order to simplify a comparison between the two implementation. However the grammar for labelled transition systems has also been extended in order to allow for quoted labels in the labelled transition system grammar, which appeared in some instances used for testing, and more convenient precedence rules for the $mu$-calculus grammar, which helped when writing some more complex formulas.

=== Performance comparison

We compared the performance of our implementation with respect to LCSFE and mCRL2 on the mCRL2 examples used originally in @flori. All the tests were performed on a computer equipped with an AMD Ryzen 3700x and 32GB of DDR4 RAM running Windows 10. LCSFE and our implementation were compiled using the Rust release profile, which applies optimizations to the code produced.

We started with the "bridge referee" example from mCRL2, modeling the crossing of a bridge by a group of 4 adventurers with different speeds, with the additional restrictions that only 2 explorers can cross the bridge at a time and that they have to carry their only flashlight at every crossing. This leads to a labelled transition system with 102 states and 177 transitions, representing all the possible ways they can try crossing such bridge. The formula to check is $mu x. diam(#h(0em)"report"(17)) #h(0.3em) tt or diam(tt) #h(0.3em) x$, representing the fact that all 4 adventurers reach the other side in 17 minutes, which is signaled by the transition $"report(17)"$. The formula thus checks if it is possible to ever execute such transition.

Using the workflow suggested by mCRL2 we first converted the mCRL2 specification into its internal lps format using the `mcrl22lps` utility:

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

We used this small example to get some empirical evidence that our implementation for $mu$-calculus is correct, as it gives the same result as the other tools, and to also show the process we used to run all the tools involved. From now on we will omit the specific commands we ran and instead will only report the time required to run them.

// TODO: Explain gossip
We then tested the second formula that was used in @flori, which uses the bigger "gossip" labelled transition system, also an example from mCRL2 which models a group of $n$ girls sharing gossips through phone calls. We tested up to $n = 5$, which leads to 9152 states and 183041 transitions, after which the transition system began growing too big. The formula tested was $nu x. diam(tt) tt and boxx(tt) x$, which represents the lack of deadlocks. It should be noted that formulas checking for absence of deadlock that are satisfied, like this one, are a worst case for local algorithms because they require visiting the whole graph, thus vanishing the advantage of local algorithms which consists in the possibility of visiting only the states that are relevant.

#figure(
  table(
    columns: (auto,) * 5,
    align: horizon,
    inset: (x: 1em),
    stroke: none,
    table.header([$n$], [*mCRL2*], [*AUT generation*], [*Our solver*], [*LCSFE*]),
    table.hline(),
    [2], [67.8 ms], [54.7 ms], [132 #us], [65.5 #us],
    [3], [68.5 ms], [59.2 ms], [212 #us], [195 #us],
    [4], [72.0 ms], [117 ms],  [2.30 ms], [4.38 ms],
    [5], [1.47 s],  [2.05 s],  [202 ms],  [5.90 s],
  ),
  caption: [Gossips benchmark results]
) <table-gossips-benchmarks>

Our implementation scales much better than LCSFE, confirming that the different parity game solving algorithm does make a difference in this case, to the point where the bottleneck becomes the generation of the AUT file, which takes an order of magnitude more time than solving the parity game itself. Compared with mCRL2 our implementation overall takes a similar amount of time, most of which is however spent doing conversions to produce the AUT file using mCRL2 itself. This suggests that lazily generating the labelled transition system might be beneficial, though this was considered out of scope for our work. Overall the pure mCRL2 approach is slightly faster, probably due to the costs of the intermediate conversions to produce the AUT file or the overhead of using a local algorithm in a case where all states must be explored regardless.

We also compared our tool with LCSFE on a set of randomly generated transition systems given the number of states, the number of transitions for each state, and the number of labels. For sake of simplicity the labels have been given a natural number starting from $0$ as their name. We used the two tools to test a _fairness_ formula on these transition systems, that is a formula in the shape $nu x. mu y. (P and diam(Act) x) or diam(Act) y$, which is satisfied when there exist a path in the labelled transition system where $P$ is true infinitely often. We choose such formula because it represents a common property to verify, it actually uses nested fixpoints, and also because it does not require exploring the whole transition system to verify, hence favoring local solvers. As a formula $P$ we choose $diam(0) tt and diam(1) tt and diam(2) tt$, that is we require a state to be able to do three transitions with respectively the labels $0$, $1$ and $2$, because it is an arbitrary condition that we can manipulate how often it is satisfied by changing the number of transitions and labels. We then tested on a number of states ranging from $1000$ to $10000$, while the number of transitions and labels tested was respectively 10/10 and 20/100, representing a case where the condition $P$ was satisfied quite often and a bit rarer.

#let size_cell(s, t, l) = (
  table.cell(align: right)[#s],
  [/],
  table.cell(align: center)[#t],
  [/],
  table.cell(align: left)[#l]
)

#figure(
  table(
    columns: (auto, 0em, auto, 0em, auto, auto, auto),
    align: center + horizon,
    inset: (x: 1em),
    stroke: none,
    table.header(table.cell(colspan: 5)[*Size (states/ \ transitions/labels)*], [*Our solver*], [*LCSFE*]),
    table.hline(),
    ..size_cell(1000, 10, 10),  [2.74 ms], [21.8 ms],
    ..size_cell(2500, 10, 10),  [5.10 ms], [59.9 ms],
    ..size_cell(5000, 10, 10),  [10.2 ms], [120 ms],
    ..size_cell(10000, 10, 10), [18.5 ms], [250 ms],
    ..size_cell(1000, 20, 100), [5.63 ms], [26.6 ms],
    ..size_cell(2500, 20, 100), [13.8 ms], [67.7 ms],
    ..size_cell(5000, 20, 100), [40.1 ms], [142 ms],
    ..size_cell(10000, 20, 100), [48.6 ms], [298 ms],
  ),
  caption: [Random LTS benchmark results]
) <table-random-fairness-benchmarks>

Again we can see our tool improving compared to LCSFE, though this time by not so much. This could be attributed to a difference in either the efficiency of the algorithm of the one of the implementation though.

Finally, we also ran our solver on some of the instances in the VLTS benchmark suite to understand the limitations and the strengths of our implementation. For each chosen instance we verified the $mu$-calculus formulas $nu x. diam(tt) tt and boxx(tt) x$, which checks for absence of deadlocks, and $mu x. diam(tt) x or (mu y. diam(#h(0em)"tau"#h(0em)) y)$, which checks for the presence of livelocks, that is cycles consisting of only tau transitions. For each instance we ran the solver 5 times, ignored the slowest and quickest ones and reported a mean of the remaining 3.

#[
  #set text(size: 10pt)
  #figure(
    table(
      columns: (auto, 4.5em, 4.5em, 4.5em, auto, 4.5em, auto),
      align: horizon,
      inset: (x: 0.3em),
      stroke: none,
      table.header([*Name*], [*States count*], [*Trans. count*], [*Deadlocks?*], [*Deadlock solve time*], [*Livelocks?*], [*Livelock solve time*]),
      table.hline(),
      `vasy_0_1`, [289], [1224], [no], [4.93 ms], [no], [6.06 ms],
      `cwi_1_2`, [1952], [2387], [no], [8.74 ms], [no], [13.4 ms],
      `vasy_52_318`, [52268], [318126], [no], [443 s], [yes], [34.9 s],
      `vasy_69_520`, [69754], [520633], [yes], [122 ms], [no], [6.09 s],
      `vasy_720_390`, [720247], [390999], [yes], [82 ms], [no], [3.40 s],
    ),
    caption: [VLTS benchmark results]
  ) <table-vlts-benchmarks>
]

The various labelled transition systems reported in @table-vlts-benchmarks have different sizes, and some have deadlocks and livelocks while others do not, which greatly influences the results and makes the various results not directly comparable to one another. We can for example see that checking for the absence of deadlocks when they are not present quickly becomes very slow, like in `vasy_52_318` where in particular we observed that even single iterations of the strategy iteration algorithm become quite slow. Checking for livelocks instead appears to be generally slower when the answer is negative, because in those cases it does not suffice to find the cycle with tau transitions but instead all the graph needs to be considered.

In the `cwi_1_2` we observed the computation of play profiles for newly expanded vertices to be especially effective, allowing the valuation step to be performed only once.

The `vasy_720_390` instance is also interesting because it is not connected, with only 87740 states which are actually reachable from the initial one. This is a favorable case for local algorithms, and in fact the time required to verify the formulas is proportional to the number of actually reachable states rather than the full amount.

== Testing with bisimilarity

We also briefly tested performance of our bisimilarity checker implementation. For that we used some of the instances mentioned above, in particular `vasy_0_1` and `cwi_1_2` because bigger instances were too slow to check. For each instance we obtained a reduced version of them according to strong bisimilarity and then used our implementation to check whether random states in the original instance were bisimilar with the ones in the reduced one.


#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: center + horizon,
    inset: (x: 1em),
    stroke: none,
    table.header(table.cell(rowspan: 2)[*Name*], table.cell(rowspan: 2)[*Bisimilar*], table.cell(colspan: 2)[*Non bisimilar*], [*Min*], [*Max*]),
    table.hline(),
    `vasy_0_1`, [15.4 ms], [540 #us], [80 ms],
    `cwi_1_2`, [5.63 s], [1.17 ms], [5.73 s],
  ),
  caption: [Bisimilarity benchmark results]
) <table-bisimilarity-benchmarks>

We splitted the results based on whether the two states were bisimilar or not, as that influences how many states the local algorithm has to consider. We also noticed that when checking non bisimilar states the time needed varied a lot, which we suspect was due to some states having lot of transitions with the same label and thus causing lot of pairs of states to be checked before becoming distinguishable.

It should be noted that strong bisimilarity admits an algorithm that runs in $O(M log N)$ @bisimilaritymlogn time, where $N$ is the number of states and $M$ the number of transitions. In comparison, for states that are bisimilar the solver needs to visit at least as many vertexes as states, similarly to the deadlock case for $mu$-calculus, leading to a complexity of $O(N dot M)$ for each the improvement step, let alone the whole algorithm. 

Ultimately the goal was to show that the powerset game was flexible enough, and being able to solve bisimilarity too, although a bit inefficiently, does confirm it.

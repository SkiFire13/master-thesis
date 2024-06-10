#let baseline-list(body) = {
  show list.item: it => context [
    #let marker = list.marker.at(0)
    #let height = measure[#it.body].height
    #box(height: height)[#marker #it.body]\
  ]
  body
}


#let environment(name) = {
  let env_counter = counter(name)
  (subject, body) => block(inset: (y: 5pt))[
    #set block(spacing: 1em)
    *#name #env_counter.step() #env_counter.display()*
    (#subject).
    _#(body)_
  ]
}

#let definition = environment("Definition")
#let lemma = environment("Lemma")
#let example = environment("Example")
#let notation = environment("Notation")
#let theorem = environment("Theorem")

#let sub = math.class("relation", sym.subset.eq.sq)
#let meet = math.class("unary", sym.sect.sq)
#let join = math.class("unary", sym.union.sq)

#let lfp = math.class("unary", sym.mu)
#let gfp = math.class("unary", sym.nu)

#let tup(a) = math.bold(a)
#let range(end) = math.underline(end)
#let XX = math.bold("X")

#let syseq(x) = math.lr(sym.brace.l + block(math.equation(x, block: true, numbering: none)))
#let feq = math.scripts("=")
#let sol = math.op("sol")

#let varempty = text(font: "", sym.emptyset)
#let disjunion = math.accent(sym.union, ".")
#let eq-columns(..cols) = stack(
  dir: ltr,
  h(1fr),
  ..cols.pos().map(align.with(horizon)).intersperse(h(1fr)),
  h(1fr),
)

#let dom = math.op("dom")

#let w0 = $w_0$
#let l0 = $l_0$
#let w1 = $w_1$
#let l1 = $l_1$

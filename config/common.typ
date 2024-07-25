#let baseline-list(body) = {
  show list.item: it => context [
    #let marker = list.marker.at(0)
    #let height = measure[#it.body].height
    #box(height: height)[#marker #it.body]\
  ]
  body
}

#let _real_label = label

#let environment(name) = {
  let env_counter = counter(name)
  let fig_counter = counter(figure.where(kind: name))
  (subject, label: none, body) => block(inset: (y: 5pt))[
    #context {
      let env_counter_val = env_counter.get().at(0)
      let head_counter_val = counter(heading).get().at(0)
      if env_counter_val != head_counter_val {
        env_counter.update((head_counter_val, 0))
        fig_counter.update(0)
      }
    }
    #set block(spacing: 1em)
    *#name #env_counter.step(level: 2) #env_counter.display()*
    #box[#figure(none, kind: name, supplement: name, numbering: (n) => [#counter(heading).display((..nums) => nums.pos().at(0)).#n])#label]
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

#let up = math.class("unary", sym.arrow.t)
#let psub = math.class("binary", $scripts(sub)^and$)
#let hsub = math.class("binary", $scripts(sub)_H$)
#let phsub = math.class("binary", $scripts(sub)_H^and$)

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
#let eq-columns(..cols) = box(stack(
  dir: ltr,
  h(1fr),
  ..cols.pos().map(align.with(horizon)).intersperse(h(1fr)),
  h(1fr),
))

#let mathstr(s) = s.clusters().map(s => $#s$).join()
#let Act = mathstr("Act")
#let Prop = mathstr("Prop")
#let Var = mathstr("Var")
#let tt = mathstr("true")
#let ff = mathstr("false")
#let sem(of) = $bracket.l.double of bracket.r.double$

#let bisim = sym.tilde.equiv

#let dom = math.op("dom")

#let w0 = $w_0$
#let l0 = $l_0$
#let w1 = $w_1$
#let l1 = $l_1$

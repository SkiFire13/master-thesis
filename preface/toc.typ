#let extra-outline(title: none, target: none) = context {
  if query(target).len() != 0 {
    if query(target).any(it => it.caption == none) {
      panic("Figure without caption")
    }
    outline(title: title, indent: auto, target: target, fill: repeat([.]))
  }
}

#let toc() = page[
  #show outline.entry.where(level: 1): it => {
    show repeat: none
    v(12pt, weak: true)
    smallcaps(it)
  }

  #outline(title: [= Index], indent: auto)
  #extra-outline(title: [= Index of figures], target: figure.where(kind: image))
  #extra-outline(title: [= Index of tables], target: figure.where(kind: table))
]

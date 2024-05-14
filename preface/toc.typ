#let toc() = page[
  #show outline.entry.where(level: 1): it => {
    show repeat: none
    v(12pt, weak: true)
    smallcaps(it)
  }

  #outline(title: [= Index], indent: auto)
]

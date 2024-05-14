#import "../config/translated.typ": *

#let titlepage(affiliation, title, supervisor, candidate, academic-year) = page(footer: "", align(center)[
  #text(size: 17pt, strong(affiliation.university))

  #text(size: 14pt, smallcaps(affiliation.department))

  #text(size: 12pt, smallcaps(affiliation.degree))

  #v(30pt)
  #image(height: 6cm, "../images/unipd-logo.png")
  #v(30pt)

  #text(size: 17pt, strong(title))

  #text(size: 12pt, style: "oblique", degree)

  #v(40pt)

  #text(size: 12pt)[
    #align(left)[
      _ #supervisor-prefix _

      #supervisor
    ]
    
    #align(right)[
      _ #candidate-prefix _

      #candidate.name

      #candidate.id
    ]
  ]

  #v(40pt)
  #line(length: 90%)
  #smallcaps[ #academic-year-prefix #academic-year ]
])

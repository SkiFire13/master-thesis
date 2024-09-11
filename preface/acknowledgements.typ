#import "../config/translated.typ": acknowledgements

#let acknowledgements-bookmark = context hide(place(dy: -page.margin.top)[
  #let acknowledgements = acknowledgements.at(text.lang)
  = #acknowledgements #label(acknowledgements)
])

#let acknowledgements() = page[
  #acknowledgements-bookmark

  #show quote: box.with(width: 70%)
  #show quote: align.with(right)
  #set quote(block: true, quotes: true)
  #quote(attribution: [Edsger W. Dijkstra])[
    _Program testing can be used to show the presence of bugs, but never to show their absence_
  ]

  #v(1cm)

  #heading(outlined: false)[Acknowledgements]

  #v(1cm)

  I thank Prof. Paolo Baldan, my thesis supervisor, for his help, mentoring and all the insightful observations he gave me while writing this thesis.

  #v(0.3cm)

  I am particularly grateful to my parents Giuseppe and Maria Grazia and my sister Francesca for their love and support as they allowed me to chase my dreams.

  #v(0.3cm)

  I thank all my friends for they company and all the laughs we had together in these years.
]

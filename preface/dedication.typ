#import "../config/translated.typ": dedication

#let dedication-bookmark = context hide(place(dy: -page.margin.top)[
  #let dedication = dedication.at(text.lang)
  = #dedication #label(dedication)
])

#let dedication() = page[
  #dedication-bookmark

  #align(center)[
    #lorem(8) \
    --- Oscar Wilde
  ]

  #v(1cm)

  #align(center)[
    Dedicato a...
  ]
]

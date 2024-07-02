#import "config/printed.typ": pagebreak-to-right, pagebreak-to-left

#import "preface/titlepage.typ": titlepage
#import "preface/copyright.typ": copyright
#import "preface/dedication.typ": dedication
#import "preface/summary.typ": summary
#import "preface/acknowledgements.typ": acknowledgements
#import "preface/toc.typ": toc

#let template(
  affiliation: (
    university: "University of Padua",
    department: [Department of Mathematics "Tullio Levi-Civita"],
    degree: "Master Degree in Computer Science",
  ),
  title: "Titolo della tesi",
  subtitle: "Tesi di laurea",
  supervisor: "Prof. Nome Cognome",
  candidate: (
    name: "Nome Cognome",
    id: 1234256
  ),
  academic-year: "AAAA-AAAA",

  keywords: (),

  lang: "it",
  date: datetime.today(),

  body
) = {
  set document(
    title: title,
    author: candidate.name,
    keywords: keywords,
    date: date,
  )

  set page(
    margin: (top: 1in + 22pt + 18pt + 12pt),
    header-ascent: 12pt + 18pt
  )
  set text(lang: lang)
  set text(font: "New Computer Modern", size: 11pt)

  {
    set heading(numbering: none)

    set page(numbering: "i")
    titlepage(
      affiliation,
      title,
      supervisor,
      candidate,
      academic-year
    )
    copyright(candidate.name, title, date)
    pagebreak-to-right(weak: true)
    dedication()
    pagebreak-to-right(weak: true)
    summary()
    pagebreak-to-right(weak: true)
    acknowledgements()
    pagebreak-to-right(weak: true)
    toc()
    pagebreak-to-right(weak: true)
  }

  {
    set page(numbering: "1")
    counter(page).update(1)
    
    set heading(numbering: "1.1.1")
    show heading.where(level: 1): it => {
      pagebreak-to-right(weak: true)
      text(size: 24pt, it)
      v(1.5em)
    }
    show heading.where(level: 2): it => {
      text(size: 18pt, it)
      v(0.5em)
    }

    set list(indent: 0.5em)
    
    show math.equation: it => {
      show ".": math.class("punctuation", ".")
      it
    }

    set par(justify: true)

    body
  }
}

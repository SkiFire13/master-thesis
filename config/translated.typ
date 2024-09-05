#let translated(..dict) = context dict.named().at(text.lang)

#let degree = translated(
  it: [ Tesi di Laurea ],
  en: [ Master thesis ],
)
#let supervisor-prefix = translated(
  it: [ Relatore ],
  en: [ Supervisor ],
)
#let candidate-prefix = translated(
  it: [ Laureando ],
  en: [ Candidate ],
)
#let academic-year-prefix = translated(
  it: [ Anno accademico ],
  en: [ Academic year ],
)

#let acknowledgements = (
  it: "Ringraziamenti",
  en: "Acknowledgements",
)

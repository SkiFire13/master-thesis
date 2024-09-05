#import "template.typ": template

#show: template.with(
  affiliation: (
    university: "University of Padua",
    department: [Department of Mathematics "Tullio Levi-Civita"],
    degree: "Master Degree in Computer Science",
  ),

  title: [Solving Systems of Fixpoint Equations \ via Strategy Iteration],
  subtitle: "Master thesis",

  supervisor: "Prof. Paolo Baldan",
  candidate: (
    name: "Giacomo Stevanato",
    id: 2078263,
  ),

  academic-year: "2023-2024",
  
  keywords: ("fixpoint", "parity games", "strategy iteration"),

  lang: "en",
)

#include "chapters/1-introduction.typ"
#include "chapters/2-background.typ"
#include "chapters/3-algorithm.typ"
#include "chapters/4-implementation.typ"
#include "chapters/5-conclusion.typ"

#bibliography("sources.bib", style: "bib-style.csl")

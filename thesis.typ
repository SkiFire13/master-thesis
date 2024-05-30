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
  
  keywords: ("keyword1", "keyword2", "keyword3"),

  lang: "en",
)

#include "chapters/introduction.typ"
#include "chapters/background.typ"
#include "chapters/algorithm.typ"

#import "conf.typ": details, generateAll
#import "@preview/oxifmt:1.0.0": strfmt
#set heading(numbering: "1.1")
#generateAll()
#set page(numbering: "1")

#show figure.where(kind: image): set figure(supplement: "Рис.")
#show figure.where(kind: table): set figure(supplement: "Табл.")

#include "sections/01.typ"
#include "sections/02.typ"
#import "@preview/ctheorems:1.1.3": *
#import "@preview/codelst:2.0.2": sourcecode

#let project(
    title: "",
    authors: (),
    date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
    body) = {
  set document(author: authors, title: title)

  set page(numbering: "1", number-align: center)

  set heading(numbering: "1.1")

  set text(size: 8pt, font: "Shippori Mincho B1 OTF", lang: "ja")

  show math.equation: set text(font: ("New Computer Modern Math", "Shippori Mincho B1 OTF"))

  show raw: set text(font: ("JuliaMono", "Noto Sans JP"))

  show raw.where(block: false): box.with(
    fill: luma(240),
    inset: (x: 4pt, y: 0pt),
    outset: (y: 3pt),
    radius: 4pt,
  )
  
  show raw.where(block: true): block.with(
    fill: luma(240),
    inset: 10pt,
    radius: 4pt,
  )
  
  set raw(lang: "lean")

  show link: set text(fill: blue)

  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  pad(
    top: 0.5em,
    bottom: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      align(center)[#date.at(0)/#date.at(1)/#date.at(2)],
      ..authors.map(author => align(center, strong(author))),
    ),
  )

  set par(justify: true)

  body
}

#let sqthmbox(name, title, base: "heading") = thmbox(name, title, stroke: luma(230), base: base)

#let barthmbox(name, title) = thmbox(
    name,
    title,
    stroke: (
      left: (thickness: 1pt, paint: luma(230))
    ),
    inset: (left: 12pt, top: 5pt, bottom: 8pt),
    radius: 0pt
  )

#let lemma = sqthmbox("lemma", "補題")

#let theorem = sqthmbox("theorem", "定理")

#let theoremq = sqthmbox("theoremq", "定理?")

#let corollary = sqthmbox("corollary", "系", base: "theorem")

#let definition = barthmbox("definition", "定義")

#let remark = barthmbox("remark", "Remark")

#let example = barthmbox("example", "例")

#let proof = thmproof("proof", "Proof")

#let struct(body) = {
  rect(
    width: 100%,
    stroke: (left: (thickness: 1pt, paint: luma(230))),
    inset: (left: 12pt, top: 5pt, bottom: 8pt))[#body]
  }

#let code = sourcecode.with(
  numbers-start: 40,
  gutter: 1em,
  frame: block.with(
    radius: 0pt,
    fill: luma(250),
    stroke: (left: 1pt + luma(20)),
    inset: (x: 1.5em, y: 1em),
  ),
)

#let brak(..args) = {
  let a = args.pos().join(", ")
  $lr(angle.l #a angle.r)$
  }

#let proves = $tack.r$
#let nproves = $tack.r.not$

#let uprsans(X) = $upright(sans(#X))$
#import "@preview/tablex:0.0.8": *

#set page(
  margin: 1cm,
  width: 600pt,
  height: 210pt,
)
#set text(size: 15pt, font: "Ubuntu")

#let rounded(color, width: auto, content) = box(
  radius: 2pt,
  fill: color,
  stroke: (
    thickness: 2pt,
    paint: color.darken(30%).desaturate(50%)
  ),
  inset: 5pt,
  width: width,
  content
)

#let container(color, name, ..items) = rounded(
  color,
  align(left, stack(dir: ttb,
    spacing: 5pt,
    box(
      fill: color.lighten(80%).saturate(90%),
      radius: 2pt,
      inset: 2pt,
      {
        set text(size: 20pt)
        raw(lang: "rust", name)
      }
    ),
    stack(dir: ltr, spacing: 5pt, ..items)
  ))
)

#let byte-size = 20pt;
#let largest = byte-size * 4;

#let vec-layout = container(
  color.hsl(100.68deg, 46.46%, 75.1%),
  "Vec<Enum>",
  rounded(color.hsl(215.49deg, 53.38%, 73.92%), width: largest, "Enum::A"),
  rounded(color.hsl(276.34deg, 53.38%, 73.92%), width: largest, "Enum::B"),
  rounded(color.hsl(330.42deg, 53.38%, 73.92%), width: largest, "Enum::C"),
  rounded(color.hsl(64deg, 100%, 79.41%), width: largest, "Enum::D"),
  rounded(color.hsl(124.92deg, 85.92%, 72.16%), width: largest, "Enum::E"),
)

#let cmem-layout = container(
  color.hsl(171.86deg, 46.46%, 75.1%),
  "ContiguousMemory",
  rounded(color.hsl(215.49deg, 53.38%, 73.92%), width: largest, "A"),
  rounded(color.hsl(276.34deg, 53.38%, 73.92%), width: byte-size, "B"),
  h(byte-size + 4pt),
  rounded(color.hsl(330.42deg, 53.38%, 73.92%), width: byte-size * 2, "C"),
  rounded(color.hsl(64deg, 100%, 79.41%), width: byte-size * 2, "D"),
)

#let cmem-layout-after = container(
  color.hsl(171.86deg, 46.46%, 75.1%),
  "ContiguousMemory",
  rounded(color.hsl(215.49deg, 53.38%, 73.92%), width: largest, "A"),
  rounded(color.hsl(276.34deg, 53.38%, 73.92%), width: byte-size, "B"),
  rounded(color.hsl(124.92deg, 85.92%, 72.16%), width: byte-size, "E"),
  rounded(color.hsl(330.42deg, 53.38%, 73.92%), width: byte-size * 2, "C"),
  rounded(color.hsl(64deg, 100%, 79.41%), width: byte-size * 2, "D"),
)

#stack(
  dir: ttb,
  vec-layout,
  v(10pt),
  align(horizon, stack(dir: ltr, spacing: 1pt,
    cmem-layout, raw(lang: "rust", ".push(E)"), $ arrow.filled $, h(5pt), cmem-layout-after
  )),
  v(5pt),
  move(dx: 100pt, text(size: 10pt)[
    #table(align: center, stroke: none, inset: 0pt, $arrow.filled.t$, v(5pt), [_alignment_], v(2pt), [_padding_])
  ])
)
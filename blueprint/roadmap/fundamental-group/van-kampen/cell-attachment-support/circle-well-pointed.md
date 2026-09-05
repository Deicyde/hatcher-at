---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Circle.wellPointedAt_one
---

# The circle is well-pointed at one

The standard basepoint `1 ∈ S¹` has an open neighborhood that strongly
contracts to `1`. Consequently the pointed-wedge theorem applies to arbitrary
families of circles without an additional geometric hypothesis.

Formalized as `Hatcher.Circle.wellPointedAt_one` in
`Hatcher/Circle/WellPointed.lean`. The proof uses the stereographic chart
centered at `-1`, which identifies its open source with a real topological
vector space and sends `1` to the origin. Scalar contraction in the chart
fixes that origin throughout.

The same module exposes `Hatcher.WellPointedAt.of_open_homeomorph_zero`, a
general criterion for proving that a point is well-pointed from such a chart.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, wedge and presentation-complex applications](../../../../sources/hatcher-1-2.md)

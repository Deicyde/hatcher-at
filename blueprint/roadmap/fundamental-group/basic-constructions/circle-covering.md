---
article_id: af_88db0f1093e08d3ab00257ce
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Circle.isCoveringMap_expMap
---

# The real line covers the circle

Hatcher's proof of Theorem 1.7 runs along `p : ℝ → S¹`,
`p(s) = (cos 2πs, sin 2πs)`, and needs only that `p` is a covering map. He
verifies this directly (page 29): every open arc of `S¹` is evenly covered.

This node supplies the same fact for Mathlib's `Circle`, the unit circle in `ℂ`.
Mathlib already has `AddCircle.isCoveringMap_coe`, that the quotient
`ℝ → AddCircle T` is a covering map, and `AddCircle.homeomorphCircle'`, a
homeomorphism `AddCircle (2 * π) ≃ₜ Circle`. Composing a covering map with a
homeomorphism is again a covering map, so the work is assembling the two and
fixing the resulting map's normalization so that the generator of the deck
group is the loop of degree one.

Hatcher does not state this as a numbered result; it is the bridge from his
concrete `p` to the Mathlib formulation, which is why its origin is `bridged`
rather than `cited`.

Formalized in `Hatcher/Circle/Covering.lean` as
`Hatcher.Circle.isCoveringMap_expMap`, with `Hatcher.Circle.expMap` the
period-one map itself. The file also proves `Hatcher.Circle.expMap_eq_one`,
that the fibre over the basepoint is exactly `ℤ`. That is the normalization
this node promised: a loop lifting to a path from `0` to `n` has winding number
`n` with no factor of `2 * π` to divide out, which is what
[winding number](winding-number.md) consumes.

## Depends on

No roadmap prerequisites. Rests only on Mathlib's `AddCircle.isCoveringMap_coe`
and `AddCircle.homeomorphCircle'`.

## Sources

- [Hatcher §1.1, Theorem 1.7 and the covering-space facts on page 29](../../../sources/hatcher-1-1.md)

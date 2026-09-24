---
article_id: af_c01ebb7ebd5194958368a3f5
source_units: [hatcher-1-3-selected-spine]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.range_mapOfEq_basepointChange
---

# Changing the lifted basepoint conjugates the image subgroup

For a path-connected covering of `(X,x₀)`, changing the chosen point in the
fiber from `e₀` to `e₁` changes the induced image subgroup by conjugation with
the class of the projection of any path from `e₀` to `e₁`. Conversely, every
conjugate is realized by lifting a representative loop from `e₀`.

Formalized as `Hatcher.Covering.range_mapOfEq_basepointChange` in
`Hatcher/Covering/BasepointChange.lean`. The same file proves the converse
`Hatcher.Covering.exists_basepoint_range_eq_map_conj` by taking the monodromy
endpoint of a representative class. The Lean theorem assumes the connecting
path explicitly, so it does not need a global path-connectedness hypothesis.

The source writes the new subgroup as `g⁻¹ H g`. Mathlib's fundamental-group
multiplication reverses Hatcher's first-then path concatenation, so the Lean
statement becomes `g H g⁻¹`, represented by `H.map (MulAut.conj g)`.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [The fundamental group acts on a covering fiber](monodromy-action.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)

## Sources

- [Hatcher §1.3, proof of Theorem 1.38 on pages 67–68](../../../sources/hatcher-1-3.md)

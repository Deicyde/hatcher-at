---
declaration: proposition
origin: cited
---

# A map lifts exactly when its fundamental group lands in the covering subgroup

**Hatcher, Proposition 1.33 (pages 61–62).** Let `Y` be path-connected and
locally path-connected. A pointed continuous map `f : (Y,y₀) → (X,x₀)` has a
pointed lift through `p : (E,e₀) → (X,x₀)` if and only if

`range(f∗) ≤ range(p∗)`.

Intended artifact: `Hatcher.Covering.exists_lift_iff_range_le`.

The pinned theorem
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` proves the hard
direction and uniqueness. The reverse implication is functoriality of induced
fundamental-group maps after a lift is supplied. Do not add a semilocal simple
connectivity hypothesis on `X`; Hatcher's criterion does not need one.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, Proposition 1.33](../../../sources/hatcher-1-3.md)

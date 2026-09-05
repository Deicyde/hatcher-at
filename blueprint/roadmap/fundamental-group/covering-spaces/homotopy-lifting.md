---
article_id: af_f26b7fc2a604528b58cd5f39
source_units: [hatcher-1-3-selected-spine]
declaration: proposition
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.existsUnique_liftHomotopy
---

# Homotopies lift uniquely through a covering map

**Hatcher, Proposition 1.30 (page 60).** Given a covering map `p : E → X`, a
homotopy `H : I × A → X`, and a continuous lift `f₀ : A → E` of the time-zero
map, there exists a unique continuous homotopy `H̃ : I × A → E` that lifts `H`
and begins at `f₀`.

Formalized as `Hatcher.Covering.existsUnique_liftHomotopy` in
`Hatcher/Covering/HomotopyLifting.lean`.

This is a thin source-facing wrapper around
`IsCoveringMap.liftHomotopy`, `liftHomotopy_lifts`,
`liftHomotopy_zero`, and `eq_liftHomotopy_iff'`. No new subdivision proof
belongs in this node.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, Proposition 1.30](../../../sources/hatcher-1-3.md)

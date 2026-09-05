---
article_id: af_08f181ae06ce36bac8627c84
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.exists_antipodal_pair_of_three_closed_sets
---

# Three closed sets covering the sphere contain an antipodal pair

**Hatcher, Corollary 1.11 (page 33).** If the two-sphere is the union of three
closed sets, at least one of those sets contains a pair of antipodal points.

Formalized as `Hatcher.Sphere.exists_antipodal_pair_of_three_closed_sets` in
`Hatcher/Sphere/AntipodalCover.lean`. The proof applies Borsuk–Ulam to the map
whose coordinates are the distances to the first two closed sets. Equal
distances at `x` and `-x` either put both points in one of those sets, or force
both into the third set by the covering hypothesis.

The distance function is totalized for the empty-set case because Mathlib
defines `Metric.infDist x ∅ = 0`; the theorem itself retains Hatcher's three
closed-set statement.

## Depends on

- [Borsuk–Ulam for the two-sphere](borsuk-ulam-sphere.md)

## Sources

- [Hatcher §1.1, Corollary 1.11, page 33](../../../sources/hatcher-1-1.md)

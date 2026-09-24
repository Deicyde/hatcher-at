---
article_id: af_09312a15c3d8d96e43cf27d7
source_units: [hatcher-2-1-selected-spine]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Singular.point_homology
---

# Homology of a point

**Hatcher, Proposition 2.8 (page 110).** Fix the one-point model
`TopCat.of PUnit`. Its degree-zero singular homology is isomorphic to the
coefficient object `R`, and its degree-`n` homology is zero for every `n ≠ 0`.

The theorem `Hatcher.Singular.point_homology` packages both clauses. Its
supporting declarations are `pointHomologyZeroIso`, obtained from the
degree-zero augmentation, and `isZero_pointHomology`, a thin specialization of
Mathlib's theorem for totally disconnected spaces. For Hatcher's statement,
specialize the coefficient category to `AddCommGrpCat` and `R` to
`AddCommGrpCat.of ℤ`.

Formalized in `Hatcher/Singular/Homology.lean`.

## Depends on

- [Singular homology](singular-homology.md)

## Proof depends on

- [Zeroth homology is free on path components](zeroth-homology-components.md)
- [Higher homology vanishes for totally disconnected spaces](totally-disconnected-higher-homology.md)

## Sources

- [Hatcher §2.1, Proposition 2.8](../../../sources/hatcher-2-1.md)

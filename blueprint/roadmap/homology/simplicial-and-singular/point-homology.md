---
declaration: lemma
origin: cited
---

# Positive-degree homology of a point vanishes

**Hatcher, Proposition 2.8 (page 110).** Fix the one-point model
`TopCat.of PUnit`. For a coefficient object `R` and `n ≠ 0`, its degree-`n`
singular homology object is zero.

The intended declaration is `Hatcher.Singular.isZero_pointHomology`, a thin
specialization of Mathlib's theorem for totally disconnected spaces. Together
with the degree-zero component calculation, it gives the two clauses of
Proposition 2.8. For Hatcher's statement, specialize the coefficient category
to `AddCommGrpCat` and `R` to `AddCommGrpCat.of ℤ`.

## Depends on

- [Singular homology](singular-homology.md)

## Proof depends on

- [Higher homology vanishes for totally disconnected spaces](totally-disconnected-higher-homology.md)

## Sources

- [Hatcher §2.1, Proposition 2.8](../../../sources/hatcher-2-1.md)

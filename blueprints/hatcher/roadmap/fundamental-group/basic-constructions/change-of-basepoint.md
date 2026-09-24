---
article_id: af_bdc7528d23af5d56f0b7e4ef
source_units: [hatcher-1-1-basic-constructions]
declaration: def
origin: cited
mathlib: true
mathlib_declaration: FundamentalGroup.fundamentalGroupMulEquivOfPath
mathlib_file: Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean
---

# A path induces change of basepoint

**Hatcher, Proposition 1.5 (page 28).** A path `h` from `x₀` to `x₁` induces
an isomorphism `βₕ : π₁(X, x₁) ≃* π₁(X, x₀)` by conjugating a loop with `h`
and its reverse.

The pinned definition `FundamentalGroup.fundamentalGroupMulEquivOfPath` sends
a path `h : Path x₀ x₁` to an equivalence
`FundamentalGroup X x₀ ≃* FundamentalGroup X x₁`. Hatcher's displayed
orientation is therefore represented by applying the definition to `h.symm`,
or equivalently by taking the inverse of the equivalence associated to `h`.

## Depends on

- [Path concatenation gives the fundamental-group law](fundamental-group-law.md)

## Sources

- [Hatcher §1.1, Proposition 1.5, page 28](../../../sources/hatcher-1-1.md)

---
article_id: af_31b7f34b97c364b77eac9aad
source_units: [hatcher-1-1-basic-constructions]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupProdEquiv
---

# The fundamental group of a product

**Hatcher, Proposition 1.12 (page 34).** Projection onto the factors gives an
isomorphism
`π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`.

Formalized as `Hatcher.fundamentalGroupProdEquiv` in
`Hatcher/FundamentalGroup/Product.lean`. Its forward map takes a product loop
to its two coordinate loops, and its inverse forms the pointwise product of
two loops. The Lean statement does not require path-connectedness because it
works at fixed basepoints and is therefore slightly stronger than Hatcher's
ambient hypothesis.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Proposition 1.12, page 34](../../../sources/hatcher-1-1.md)

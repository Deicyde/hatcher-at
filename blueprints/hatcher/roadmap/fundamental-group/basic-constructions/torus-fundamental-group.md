---
article_id: af_7e18c86739116c84823e7c20
source_units: [hatcher-1-1-basic-constructions]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.torusFundamentalGroupEquiv
---

# The fundamental group of the torus

**Hatcher, Example 1.13 (page 34).** The fundamental group of
`S¹ × S¹` is isomorphic to `ℤ × ℤ`. Under this isomorphism, `(m, n)`
corresponds to the loop `ωₘₙ(s) = (ωₘ(s), ωₙ(s))`.

Formalized as `Hatcher.torusFundamentalGroupEquiv` in
`Hatcher/FundamentalGroup/Product.lean`. The companion theorems
`torusFundamentalGroupEquiv_prod_loopOfInt` and
`torusFundamentalGroupEquiv_symm_apply` record both directions of Hatcher's
loop formula.

## Depends on

- [The fundamental group of a product](product-fundamental-group.md)
- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, Example 1.13, page 34](../../../sources/hatcher-1-1.md)

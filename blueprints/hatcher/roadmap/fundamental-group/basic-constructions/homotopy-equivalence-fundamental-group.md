---
article_id: af_1f0895b5c7dfb77e33224fd8
source_units: [hatcher-1-1-basic-constructions]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupMulEquivOfHomotopyEquiv
---

# A homotopy equivalence induces a fundamental-group isomorphism

**Hatcher, Proposition 1.18 (page 37).** A homotopy equivalence
`e : X ≃ₕ Y` induces an isomorphism
`π₁(X, x) ≃* π₁(Y, e(x))` at every basepoint `x`.

Formalized as `Hatcher.fundamentalGroupMulEquivOfHomotopyEquiv` in
`Hatcher/VanKampen/WedgeFundamentalGroup.lean`. It is obtained from Mathlib's
equivalence of fundamental groupoids and records that the forward map is
exactly the homomorphism induced by `e.toFun`.

The companion definition
`Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq` transports the target
basepoint along a supplied equality, which is the form used by later
deformation-retract arguments.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Proposition 1.18, page 37](../../../sources/hatcher-1-1.md)

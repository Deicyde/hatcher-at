---
article_id: af_6dee64aae05fa95dd6fbcd83
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupMap_injective_of_retraction
---

# Retractions and deformation retracts on the fundamental group

**Hatcher, Proposition 1.17 (page 36).** If a space `X` retracts onto `A`,
the inclusion-induced homomorphism `π₁(A, a) →* π₁(X, a)` is injective. If
`A` is a deformation retract of `X`, that homomorphism is an isomorphism.

Formalized in `Hatcher/VanKampen/WedgeFundamentalGroup.lean`. The theorem
`Hatcher.fundamentalGroupMap_injective_of_retraction` proves the first clause
from continuous maps `A → X` and `X → A` whose composite on `A` is the
identity. The definition
`Hatcher.fundamentalGroupMulEquivOfDeformationRetract` adds a homotopy from
the identity on `X` to the inclusion followed by the retraction and produces
the equivalence in the second clause. Its companion application theorem
records that the forward homomorphism is induced by inclusion.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Proposition 1.17, page 36](../../../sources/hatcher-1-1.md)

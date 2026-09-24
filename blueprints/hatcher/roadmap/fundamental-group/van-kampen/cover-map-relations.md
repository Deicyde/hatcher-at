---
article_id: af_cdfdd640e75db0f65a9e7e19
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.relationSubgroup_le_ker
---

# Overlap relations vanish under the cover map

For Hatcher's open-cover presentation, every generator of the overlap-relation
subgroup maps to the identity under the canonical cover map. Therefore

`relationSubgroup ≤ MonoidHom.ker coverMap`,

and `coverMap` descends to a homomorphism from the quotient free product to
`π₁(X, x₀)`.

The main artifact is `Hatcher.VanKampen.relationSubgroup_le_ker`; the same file
should define the supporting map `Hatcher.VanKampen.quotientCoverMap`.

This is the formal-algebra inclusion in the kernel calculation. It should use
the universal properties of `Monoid.CoprodI`, `Subgroup.normalClosure`, and
`QuotientGroup`, without topological subdivision arguments.

Formalized in `Hatcher/VanKampen/CoverMapRelations.lean`. The file also proves
the individual relator calculation and exports the descended homomorphism
`Hatcher.VanKampen.quotientCoverMap`.

## Depends on

- [The group presentation associated to an open cover](cover-group-presentation.md)

## Sources

- [Hatcher §1.2, proof of Theorem 1.20 on page 44](../../../sources/hatcher-1-2.md)

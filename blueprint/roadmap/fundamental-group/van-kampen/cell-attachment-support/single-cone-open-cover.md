---
article_id: af_b3b1f5a35c05a79813552fed
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.isOpenCover_lower_upper
---

# A single cone attachment has a two-set open cover

For a map `f : S → X`, construct the point-set quotient of `X ⊔ {*} ⊔ (S × I)`
that collapses `S × {0}` to the explicit cone apex and glues `S × {1}` to `X`
through `f`. Later deformation results will require `f` to be continuous; the
quotient and its open cover do not.

The subsets consisting respectively of the canonical image of `X` with all
positive-height cone points, and the apex with all subunit-height cone points,
are open and cover the quotient. This is formalized by
`Hatcher.VanKampen.ConeAttachment.isOpenCover_lower_upper`; the module also
provides the endpoint quotient identities and restricted quotient maps needed
to descend the later deformation homotopies.

This node deliberately handles one augmented cone. It does not yet model an
arbitrary family of attached cells: that construction needs one apex per cell,
the deformation retractions, and a comparison with Mathlib's
`HomotopicalAlgebra.AttachCells` pushout.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, construction used in Proposition 1.26 on pages 49–51](../../../../sources/hatcher-1-2.md)

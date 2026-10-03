---
article_id: af_d2437d3f858877fb8db266dd
source_units: [hatcher-2-1-good-pair-quotient]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.GoodPairData.pointQuotientNeighborhoodStrongDeformationRetract
---

# The quotient neighborhood contracts to its point

Descend the chosen strong deformation retraction of `V` onto the embedded
subspace through the restricted quotient map `V → qV`. Construct a strong
deformation retraction of `qV` onto the collapsed point and expose its
homotopy equivalence.

The intended main declaration is
`Hatcher.Relative.GoodPairData.pointQuotientNeighborhoodStrongDeformationRetract`.
Continuity must follow from the quotient property proved for the source-exact,
not-necessarily-open neighborhood.

Formalized in
`Hatcher/Singular/PointQuotientNeighborhoodContraction.lean`. The chosen
deformation of `V` preserves the fibers of the restricted quotient: it fixes
all representatives in the collapsed subspace, while equality of two
noncollapsed representatives follows from the complement homeomorphism.
Joint continuity of the descended homotopy follows from
`pointQuotientNeighborhoodProjection_isQuotientMap.continuous_lift_prod_right`;
no openness assumption is made on `V`. The resulting strong deformation
retraction is relative to the canonical collapsed-point inclusion, and
`pointQuotientNeighborhoodHomotopyEquiv` exposes the corresponding homotopy
equivalence with that inclusion as its forward map.

## Depends on

- [Restricting the quotient to a good-pair neighborhood](good-pair-neighborhood-quotient.md)

## Sources

- [Hatcher §2.1, induced deformation retraction of `V/A`, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)

# Prescribed local degrees of the signed pinch

## Uncompiled source draft

The generic `SignedSphereFoldData.regular_point_local_degree` derives
isolation and proves the prescribed sign for every isolation witness at the
existing explicit regular fiber point. The canonical
`sphere_signed_pinch_local_degree` specializes it to the constructed signed
fold, retaining arbitrary `Fin k` component indices and regular targets.

A private proof derives the actual singleton fiber of the corrected component
`cᵢ ≫ aᵢ.hom` over the same target. Outside its actual ball the component is
constant at the omitted point, which the correction fixes. Inside, the actual
ball chart and correction inverse force the explicit regular source point.
No fiber, homeomorphism, sign or global degree is supplied as a caller premise.

The singleton comparison gives the corrected component's local degree equal
to its already proved global degree. On the actual open ball the signed map
and corrected component agree, so the reached germ invariance theorem derives
isolation of the signed map and identifies its signed local degrees for every
pair of witnesses. The constructed corrected degree is the prescribed sign.

The source adds no imports or options and preserves all earlier declarations.
No local Lean compilation has run. Remote checks must verify TopCat composite
applications, subtype/fiber equalities, the explicit point's ball membership,
EqOn direction, dependent isolation-witness arguments, signed equality
transitivity and the canonical specialization. Ordinary axioms, unused
arguments and full independent canonical/source review remain required before
completion assertions are recorded.

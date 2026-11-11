# Implementation note: The cell-sphere quotient reads its canonical cellular coordinate

## Remaining goal

For a positive-dimensional cell β, prove that the homology map of its actual complement-collapse quotient, after the fixed target sphere-generator identification, is the β-coordinate in the existing cell basis. Retain the equation for every relative class, not only individual generators.

## Candidate declaration

`Hatcher.ClassicalCW.cellCollapseCoordinates` is a naming proposal, not a verified declaration.

## Route

Use good-pair quotient naturality, the actual characteristic/wedge equations and the fixed target generator alignment. Equality on every basis class extends to all finite-support combinations.

## Fixed model and API constraints

Keep `positiveStandardDiskFundamentalClass`,
`positiveSkeletonCellFundamentalClass`, `skeletalCellFundamentalClass` and
the actual `cellularDifferential`. Their maps are in
`Hatcher/Singular/PointedWedgeHomology.lean` and
`Hatcher/Singular/Relative.lean`. Natural-number adjacent degrees are
(n+1,n); the outgoing degree-zero map is unaugmented and zero.

## Actual selected-cell projection

Use `skeletonPointQuotientIsoWedge` with its pair-map and inclusion equations
and `PointedWedge.desc` for the continuous selected summand collapse.
`positiveSkeletonCell_class_to_wedge` is private evidence of current target
sign alignment; obtain the public all-class coordinate equation through the
existing basis or a coordinated public consequence. Do not replace the
actual complement collapse by a supplied coefficient homomorphism.

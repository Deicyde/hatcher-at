# Implementation note: The cellular boundary formula

## Remaining goal

For every classical CW complex and n > 1, the actual cellular boundary of each n-cell generator is the finite sum of its constructed attaching-map degrees times the existing (n−1)-cell generators. The target cell sets may be infinite; an empty target gives the empty sum.

## Candidate declaration

`Hatcher.ClassicalCW.cellularBoundaryFormula` is a naming proposal, not a verified declaration.

## Route

The attaching-degree family has geometric finite support, each degree is the actual canonical boundary coordinate, and coordinate reconstruction gives the full equation.

## Fixed model and API constraints

Keep `positiveStandardDiskFundamentalClass`,
`positiveSkeletonCellFundamentalClass`, `skeletalCellFundamentalClass` and
the actual `cellularDifferential`. Their maps are in
`Hatcher/Singular/PointedWedgeHomology.lean` and
`Hatcher/Singular/Relative.lean`. Natural-number adjacent degrees are
(n+1,n); the outgoing degree-zero map is unaugmented and zero.

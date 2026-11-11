# Implementation note: The fixed one-disk class orders its two endpoints

## Remaining goal

Construct an explicit ordering of the two actual endpoints of the standard one-disk so that its ordinary connecting map takes the current relative disk class to terminal point class minus initial point class in ordinary H₀ of the boundary. Preserve the fixed disk class.

## Candidate declaration

`Hatcher.ClassicalCW.orientedOneDiskEndpoints` is a naming proposal, not a verified declaration.

## Route

The connecting image generates the augmentation kernel inside the ordinary two-point group. Its multiplier relative to the explicit endpoint difference is plus or minus one; select the endpoint order accordingly.

## Fixed model and API constraints

Keep `positiveStandardDiskFundamentalClass`,
`positiveSkeletonCellFundamentalClass`, `skeletalCellFundamentalClass` and
the actual `cellularDifferential`. Their maps are in
`Hatcher/Singular/PointedWedgeHomology.lean` and
`Hatcher/Singular/Relative.lean`. Natural-number adjacent degrees are
(n+1,n); the outgoing degree-zero map is unaugmented and zero.

## Endpoint order and ordinary degree zero

Ordinary H₀ of the standard zero-sphere is the two-point group, using
`Hatcher.Sphere.singularHomologyZeroIsoSphereZero`, its augmentation/codiagonal
law and `reducedHomologyZeroSphereToOrdinaryIsKernel`. Prove any needed
point-class coordinate equations explicitly when no public equation supplies them.
The fixed one-disk class maps into its augmentation kernel. Derive its unit
multiplier relative to the explicit endpoint difference and choose the order
from that sign. Identify attaching endpoints with `zeroCellPoint` and
`zeroCellRelativeClass`. A single vertex cancels the difference directly;
this route does not need a redundant connectedness hypothesis.

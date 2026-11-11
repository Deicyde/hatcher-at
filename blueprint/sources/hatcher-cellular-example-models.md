# Cell models for the first cellular homology illustrations

Source: [Hatcher, Algebraic Topology](hatcher.md), official PDF SHA-256
`bebb3032bf9021b956da3bd070eb6c67dc662cf849be9cdf6679f677560e5618`.
Printed pages 6–8 are PDF pages 15–17. These targets supply the actual
geometric models used by the unnumbered illustrations on printed page 140.
This note carries citations and paraphrased targets, not reproduced passages.

## Example 0.3

Printed page 6. A positive-dimensional sphere has a minimal CW structure
with one zero-cell and one cell in its dimension. The characteristic disk
collapses its boundary to the zero-cell. The selected model is the standard
sphere with its fixed point and actual disk-boundary quotient identification.
The construction must produce a classical CW structure, as required by the
completed cellular comparison.

## Example 0.6

Printed pages 6–7. Finite ℂPⁿ is the quotient of nonzero vectors in ℂⁿ⁺¹ by
nonzero complex scalars. The characteristic real 2n-disk is parametrized in
complex Euclidean coordinates by

\[
w \longmapsto [w,\sqrt{1-\lVert w\rVert^2}].
\]

Its interior is the chart with nonzero last coordinate. Its boundary maps to
the actual coordinate copy of ℂPⁿ⁻¹, with unit-phase identifications. This
gives the disk attachment and the even-dimensional cell pattern, starting
with the singleton ℂP⁰. The infinite-projective-space continuation is not
needed for the finite illustration.

Compact Hausdorff topology, the normalized unit-sphere phase quotient and
the affine-chart equations are supporting obligations for realizing these
maps. They are not separately quoted theorems from Example 0.6.

## Products

Printed page 8. Product cells have dimensions equal to the sums of the factor
dimensions. The finite case needed here uses the ordinary product topology;
no unrestricted product-topology assertion for arbitrary CW complexes is
adopted. The constructed sphere factors therefore give the four product
cells of Sⁿ×Sⁿ for n > 1.

## Model comparisons

Classical sup-norm cells and standard Euclidean disks must be connected by
actual disk/boundary maps. The already verified dimension-only classical-cell arrow comparison
supplies its disk and boundary maps publicly. Use those components and retain
any needed interior equations, without asserting an unproved orientation normalization.

See the [implementation specification](cellular-boundary-implementation.md)
and the [cellular-computation source passage](hatcher-2-2-cellular-boundary.md).

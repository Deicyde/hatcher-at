# Cellular boundary and first computation specification

This is a project-authored mathematical realization of
[Hatcher's next cellular passage](hatcher-2-2-cellular-boundary.md), with
[its geometric support](hatcher-cellular-example-models.md).

## Actual objects and indices

Use the completed ordinary integral cellular complex and its characteristic
cell classes. Degree n is the relative homology of the n-skeleton and its
predecessor; the predecessor of the zero-skeleton is empty. Write adjacent
maps as Cₙ₊₁ → Cₙ when working with natural-number indices. The outgoing
degree-zero map is zero, without an augmentation.

The CW carrier is the complex's own space, including when it is a subspace
of a larger Hausdorff ambient space. All general results allow arbitrary
cell sets and unbounded dimension. A finite generator bound requires only
finitely many cells in its own degree.

## Fixed generators and boundary orientation

Preserve the existing relative standard-disk classes and their actual
characteristic-map images. The previously chosen simplex and disk models
do not themselves prove that successive ordered sphere classes have a
particular connecting-map sign.

In positive boundary dimension, prove that the actual ordinary connecting
map takes the fixed disk class to a sphere generator. Compare it with the
existing ordered generator and construct the identity or reflection
identification according to the proved unit multiplier. Use that actual
source identification in the attaching-sphere map.

For the one-disk, work in ordinary H₀ of its two boundary points. Its
connecting image generates the augmentation kernel. Construct the endpoint
order from the fixed disk class, then pass those actual endpoints through
the characteristic map to the fixed vertex basis.

## Canonical sphere and coefficient transport

The degree model and the cellular class model use different canonical
space and coefficient lifts. Construct their chain comparison, its actual
simplex and ordered-class equations, and self-map naturality. Prove the
positive-degree multiplier equation in the cellular class model from those
maps and the existing reduced/ordinary comparison.

## Selected cell projections and coefficients

Construct the continuous selected-summand collapse through the actual weak
skeletal-wedge quotient. Preserve its characteristic-disk equation, the
constant values on other cells and the quotient collapsing the complement
of the selected open cell. The existing target quotient identification
determines its target orientation.

Construct coordinates of the actual cellular differential using the inverse
of the fixed free-cell isomorphism. The prescribed images of all standard
vectors make its choice unique. Prove that the selected quotient homology map
reads that coordinate, and then prove equality with the degree of the actual
attaching-sphere composite.

The geometric finite-support proof uses the compact attaching image and its
finite cell cover. Missing a target open cell makes the actual collapse
composite constant, with degree zero. This support proof is independent of
the coordinate-equality theorem. Coordinate reconstruction then gives the
complete higher boundary formula for n > 1.

## Classical structures for the examples

Construct the actual finite complex projective quotient, normalize its
nonzero-vector quotient to the compact unit-sphere phase quotient, and prove
compact Hausdorff topology. Retain the coordinate embedding, affine chart
and square-root characteristic disk with their representative and fiber
equations. Build the finite classical CW structure from those maps and its
exact even-dimensional cell indices. Its homology calculation uses the
proved no-adjacent-dimensions result.

For the sphere product, construct the minimal classical sphere structures
and their finite classical product. Classical sup-norm cell coordinates
concatenate into the product cell, including dimension-zero factors.
Enumerate the actual product cells and apply the same homology theorem for
n > 1. These constructions make no use of a supplied homology matrix or
unconstructed cell-structure certificate.

## Source coverage and proof routes

The adopted boundary contains applications (i)–(iii), both unnumbered
illustrations, the first-differential discussion and the complete higher
boundary formula through its diagram derivation. The needed finite parts of
Examples 0.3 and 0.6 and the Products paragraph are included as geometric
support. The finite-dimensional alternative proof remark is explanatory.

Use the existing PID basis and finite independent-family bounds for the
subgroup argument, then pass a genuine generating family through the
quotient. The homology group itself may have torsion. The finite classical
CW constructor verifies weak topology once the actual maps, disjoint
interiors, boundary containment and finite cover are supplied.

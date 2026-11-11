# Hatcher §2.2: first cellular computations and the boundary formula

Source: [Hatcher, Algebraic Topology](hatcher.md), Cambridge University Press,
2002. The official PDF has SHA-256
`bebb3032bf9021b956da3bd070eb6c67dc662cf849be9cdf6679f677560e5618`.
Printed pages 140–141 are PDF pages 149–150. The adopted passage starts after
the proof of Theorem 2.35 and stops before Example 2.36. This page records
citations and paraphrased mathematical targets.

## Immediate applications

Printed page 140, applications (i)–(iii). Homology in degree n vanishes when
there are no n-cells. With k n-cells, k finite, it has at most k generators;
the cycle subgroup is free before taking the quotient, while the homology
group may have torsion. If occupied cell dimensions are never adjacent, the
cellular differentials vanish and homology has the actual cell basis.

The statements include degree zero, empty complexes and unbounded CW
dimension. Only the number of n-cells is finite in the generator-bound
statement. The finite-dimensional induction remark is an alternative proof
route; it adds no endpoint to the selected cellular proof.

## First geometric illustrations

Printed page 140. The complex-projective illustration gives ordinary integral
homology ℤ in the even degrees from zero through 2n and zero elsewhere for
the actual finite space ℂPⁿ. The second illustration uses the actual product
Sⁿ×Sⁿ for n > 1, with one zero-cell, two n-cells and one 2n-cell. Its homology
is therefore ℤ in degrees zero and 2n, ℤ⊕ℤ in degree n and zero elsewhere.
These are unnumbered illustrations; neither is Example 2.36.

Their needed geometric sources are recorded in
[the cell-model source note](hatcher-cellular-example-models.md). The adopted
targets construct classical CW structures on the actual spaces, with their
characteristic maps and exact cell indices.

## First differential

Printed page 140, immediately before the boundary formula. The first
cellular differential is the endpoint boundary of an oriented one-cell.
The book observes that it is zero for a connected complex with one zero-cell.
The selected endpoint proof derives the stronger one-vertex statement directly:
both actual endpoints are that vertex, so their difference is zero.

The endpoint order must agree with the fixed relative one-disk class. Its
ordinary boundary lies in the augmentation kernel of the two-point H₀ group;
ordinary H₀ of the zero-sphere is not a rank-one group.

## Higher boundary formula

Statement on printed page 140; characteristic-map definitions and derivation
on page 141. For n > 1, the coefficient of an (n−1)-cell β in the boundary
of an n-cell α is the degree of its actual attaching map followed by the
quotient collapsing the complement of β. The sum has finite support because
the compact attaching image meets finitely many target cells. Cells with
degree zero may still meet that image.

The source sphere has the boundary orientation of the chosen relative disk
class. The target sphere is the selected characteristic disk/boundary quotient.
The adopted specification preserves the already fixed cell classes and
constructs any needed orientation identification.

## Characteristic diagram

Printed page 141. The diagram connects the relative disk class to its cell
class by the actual characteristic map, and connects their boundary images by
the actual attaching map. The skeletal quotient and selected-cell collapse
read the target cell coordinate. Its sphere groups are reduced; in positive
degrees the canonical reduced/ordinary comparison relates this to the
ordinary pair maps used by the existing cellular differential. The selected
proof records those actual map equations rather than assuming a coefficient
formula.

## Adoption and continuation

The [cellular boundary and computation milestone](../roadmap/homology/computations-and-applications/cellular-boundary/README.md)
continues the completed seventeen-leaf cellular/singular comparison.
Surface computations beginning with Example 2.36, Moore spaces, Euler
characteristic and later coefficient material remain queued for later passes.

The [implementation specification](cellular-boundary-implementation.md) is
project-authored mathematical support. Its coefficient and sphere-model
comparisons are required by the selected realization, rather than additional
claims attributed to Hatcher's printed paragraph.

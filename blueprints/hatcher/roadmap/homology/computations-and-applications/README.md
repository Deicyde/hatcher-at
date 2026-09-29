---
article_id: af_3a2b37424915dda0dbd5d97b
---

# Computations and applications

Hatcher §2.2 (pages 134–159). The binary interior-cover Mayer–Vietoris
sequence is complete in six formalizable leaves. A thirteen-leaf continuation
now covers neighborhood-retract transport, Example 2.46, and reduced sphere
homology. The remainder of the section stays explicitly deferred.

Given excision and the long exact sequence, homology becomes computable. From
`Hₙ(Sⁿ) ≅ ℤ` comes the degree of a map `Sⁿ → Sⁿ`, with its local formula as a
sum over preimages, which settles the hairy ball theorem and which finite
groups act freely on spheres. Cellular homology computes `Hₙ` of a CW complex
from its cells and attaching maps, reducing infinite singular chain groups to
finitely generated ones. Mayer–Vietoris is the homology analogue of van
Kampen. The section closes with coefficients in an arbitrary abelian group.

Brouwer's fixed point theorem in all dimensions and invariance of domain follow
here, generalizing the two-dimensional cases proved from `π₁(S¹)` in
[basic constructions](../../fundamental-group/basic-constructions/README.md).

The [Mayer–Vietoris milestone](mayer-vietoris/README.md) constructs the
ordinary and reduced exact sequences directly from the completed small-chain
equivalence. The [sphere-homology milestone](sphere-homology/README.md) adds
the conditional neighborhood-retract extension and applies it to the
hemispheres of a sphere.

Nothing in this selected slice is present in the pinned Mathlib. Mathlib has CW complexes
(`Topology/CWComplex/Classical/`) but no cellular homology, no degree theory,
and no Mayer–Vietoris for singular homology; the `MayerVietoris` files in
Mathlib are sheaf-theoretic and unrelated. TauCeti has relevant post-pin prior
art, recorded in the implementation specification, but it is neither pinned
Mathlib coverage nor a project dependency.

## Mayer–Vietoris

- [Binary-cover Mayer–Vietoris sequences](mayer-vietoris/README.md)
- [Mayer–Vietoris transport and sphere homology](sphere-homology/README.md)

Degree, cellular homology, the later Mayer–Vietoris applications, and homology
with general coefficient groups as a separate source topic remain deferred.

## Sources

- [Hatcher §2.2](../../../sources/hatcher.md)
- [Hatcher §2.2 Mayer–Vietoris source note](../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../sources/sphere-homology-implementation.md)

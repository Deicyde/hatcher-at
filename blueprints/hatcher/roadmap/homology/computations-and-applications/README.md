---
article_id: af_3a2b37424915dda0dbd5d97b
---

# Computations and applications

Hatcher §2.2 (pages 134–159), together with the selected sphere applications
from §2.1. The binary interior-cover Mayer–Vietoris sequence is complete in six
formalizable leaves. The thirteen-leaf continuation covering
neighborhood-retract transport, Example 2.46, and reduced sphere homology is
also complete. The three-leaf Corollary 2.15 application is complete. The
remainder of §2.2 stays explicitly deferred.

Given excision and the long exact sequence, homology becomes computable. From
`Hₙ(Sⁿ) ≅ ℤ` comes the degree of a map `Sⁿ → Sⁿ`, with its local formula as a
sum over preimages, which settles the hairy ball theorem and which finite
groups act freely on spheres. Cellular homology computes `Hₙ` of a CW complex
from its cells and attaching maps, reducing infinite singular chain groups to
finitely generated ones. Mayer–Vietoris is the homology analogue of van
Kampen. The section closes with coefficients in an arbitrary abelian group.

The selected Corollary 2.15 branch derives Brouwer's fixed-point theorem for
all positive-dimensional disks, generalizing the two-dimensional case proved
from `π₁(S¹)` in
[basic constructions](../../fundamental-group/basic-constructions/README.md).
Invariance of domain belongs to out-of-scope Additional Topic §2.B.

The completed [Mayer–Vietoris milestone](mayer-vietoris/README.md) constructs
the ordinary and reduced exact sequences directly from the completed
small-chain equivalence. The completed
[sphere-homology milestone](sphere-homology/README.md) adds the conditional
neighborhood-retract extension, applies it to the hemispheres of a sphere, and
continues through the completed no-retraction and Brouwer applications.

The pinned Mathlib supplies the standard disk, boundary, and inclusion models,
but not the selected no-retraction, Brouwer, sphere-homology, or
Mayer–Vietoris results. It has CW complexes but no cellular homology or degree
theory; its `MayerVietoris` files are sheaf-theoretic and unrelated. External
prior art is recorded in the implementation specifications but is neither
pinned Mathlib coverage nor a project dependency.

## Selected milestones

- [Binary-cover Mayer–Vietoris sequences](mayer-vietoris/README.md)
- [Mayer–Vietoris transport, sphere homology, and Brouwer](sphere-homology/README.md)

Degree, cellular homology, the later Mayer–Vietoris applications, and homology
with general coefficient groups as a separate source topic remain deferred.

## Sources

- [Hatcher §2.2](../../../sources/hatcher.md)
- [Hatcher §2.2 Mayer–Vietoris source note](../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../sources/sphere-homology-implementation.md)
- [Corollary 2.15 implementation specification](../../../sources/corollary-2-15-implementation.md)

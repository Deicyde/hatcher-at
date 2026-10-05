---
article_id: af_3a2b37424915dda0dbd5d97b
---

# Computations and applications

Hatcher §2.2 (pages 134–159), together with the selected sphere applications
from §2.1. The binary interior-cover Mayer–Vietoris sequence is complete in six
formalizable leaves. The thirteen-leaf continuation covering
neighborhood-retract transport, Example 2.46, and reduced sphere homology is
also complete. The three-leaf Corollary 2.15 application is complete. The
dependency-ordered branches formalize the §2.1 post-excision applications
through Theorem 2.26 in twenty-seven leaves, supported by five Appendix A.5
regular-neighborhood leaves. All thirty-two are complete. The remainder of
§2.2 now also has a sixteen-leaf degree-foundations milestone through
Proposition 2.29. Those new leaves are planned; the later material stays
explicitly deferred.

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

The [post-excision applications](post-excision-applications/README.md) branch
continues from Proposition 2.22 through mapping cones, explicit fundamental
cycles, CW-subcomplex excision, and wedge additivity. The separate
[local-homology branch](local-homology-and-dimension/README.md) culminates in
Theorem 2.26. These pages retain their §2.1 source binding but are placed here
so their sphere-homology prerequisites remain dependency-ordered.

The [degree-foundations milestone](degree/README.md) uses the completed
ordered sphere class to define degree, calculate reflections and the antipodal
map, prove the fixed-point-free formula, and reach Theorem 2.28 and Proposition
2.29. It stops before local degree.

The pinned Mathlib supplies the standard disk, boundary, and inclusion models,
but not the selected no-retraction, Brouwer, sphere-homology, degree, or
Mayer–Vietoris results. It has CW complexes but no cellular homology or degree
theory; its `MayerVietoris` files are sheaf-theoretic and unrelated. External
prior art is recorded in the implementation specifications but is neither
pinned Mathlib coverage nor a project dependency.

## Selected milestones

- [Binary-cover Mayer–Vietoris sequences](mayer-vietoris/README.md)
- [Mayer–Vietoris transport, sphere homology, and Brouwer](sphere-homology/README.md)
- [Post-excision applications](post-excision-applications/README.md)
- [Local homology and invariance of dimension](local-homology-and-dimension/README.md)
- [Degree foundations and applications](degree/README.md)

Local degree, degree-realization examples, suspension invariance, cellular
homology, the later Mayer–Vietoris applications, and homology with general
coefficient groups as a separate source topic remain deferred.

## Sources

- [Hatcher §2.1](../../../sources/hatcher-2-1.md)
- [Hatcher §2.2](../../../sources/hatcher.md)
- [Hatcher §2.2 Mayer–Vietoris source note](../../../sources/hatcher-2-2.md)
- [Hatcher §2.2 degree source note](../../../sources/hatcher-2-2-degree.md)
- [Sphere-homology implementation specification](../../../sources/sphere-homology-implementation.md)
- [Corollary 2.15 implementation specification](../../../sources/corollary-2-15-implementation.md)
- [Post-excision applications implementation specification](../../../sources/post-excision-applications-implementation.md)
- [Degree-foundations implementation specification](../../../sources/degree-theory-implementation.md)

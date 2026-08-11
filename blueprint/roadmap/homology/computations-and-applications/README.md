---
not_ready: true
---

# Computations and applications

Hatcher §2.2 (pages 134–159). Mapped, not yet decomposed.

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

Nothing in this section is upstream. Mathlib has CW complexes
(`Topology/CWComplex/Classical/`) but no cellular homology, no degree theory,
and no Mayer–Vietoris for singular homology; the `MayerVietoris` files in
Mathlib are sheaf-theoretic and unrelated.

## Sources

- [Hatcher §2.2](../../../sources/hatcher.md)

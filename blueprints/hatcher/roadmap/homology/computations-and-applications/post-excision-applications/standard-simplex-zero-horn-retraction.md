---
article_id: af_f95465a69adbe4843302e352
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# A standard simplex strongly deformation retracts onto its zero horn

Construct a strong deformation retraction of `Δ[n+1]` onto `Λ⁰[n+1]`.
In barycentric coordinates, subtract the minimum of the coordinates with
positive index, transfer the removed mass to coordinate zero, and interpolate
linearly from the identity. Prove continuity, preservation of the simplex,
the endpoint formula, and pointwise fixation of the horn.

The main artifact is
`Hatcher.Simplex.zeroHornStrongDeformationRetract`. It supplies the vanishing
of `H_*(Δ[n+1], Λ⁰[n+1];R)` used in the triple-sequence induction of Example
2.23.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)
- [Strong deformation retracts](../../simplicial-and-singular/relative-homology/good-pair-quotient/strong-deformation-retract.md)

## Sources

- [Hatcher §2.1, deformation retraction used in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

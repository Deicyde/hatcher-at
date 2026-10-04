---
article_id: af_f470c42e2b74bf78b5a5d459
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# Standard-simplex boundary and horn pairs are good

For a positive-dimensional standard simplex, construct chosen good-pair data
for `(Δ[n], ∂Δ[n])`. Use the complement of the barycenter as a neighborhood
of the boundary and radial normalization away from that barycenter.

For `(∂Δ[n+1], Λ⁰[n+1])`, remove the barycenter of the omitted zero face and
retract the remaining boundary onto the horn by subtracting and renormalizing
the least positive-index barycentric coordinate. The retraction must fix the
horn pointwise.

The main artifact is
`Hatcher.Simplex.boundaryZeroHornGoodPairData`; the simplex-boundary witness
is supporting data. State the positive-dimensional restriction explicitly:
the boundary of `Δ[0]` is empty, while the project's `GoodPairData` requires a
nonempty subspace.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)
- [Good pairs and neighborhood deformation retracts](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-data.md)

## Sources

- [Hatcher §2.1, good-pair quotient step in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

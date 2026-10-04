---
article_id: af_4849582f9a5a21cf759a4846
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: background
---

# The boundary and zero horn of a standard topological simplex

For the ordered topological simplex `Δ[n] :=
Convexity.StdSimplex ℝ (Fin (n + 1))`, define its boundary by the vanishing
of at least one barycentric coordinate. In `Δ[n+1]`, define the zero horn as
the union of every codimension-one face except face zero. Package the
inclusions

`Λ⁰[n+1] ⊆ ∂Δ[n+1] ⊆ Δ[n+1]`

as a `Hatcher.Relative.TopTriple`, and package the zero-face map as a morphism
of pairs

`(Δ[n], ∂Δ[n]) ⟶ (∂Δ[n+1], Λ⁰[n+1])`.

The main artifact is `Hatcher.Simplex.standardSimplexBoundaryHornTriple`.
Supporting definitions include the relative simplex pair and the identity
singular simplex obtained from `TopCat.toSSetObjEquiv`.

These are topological standard simplices and singular chains. Do not replace
them by simplicial-set homology, since the comparison with singular homology
is Theorem 2.27 and lies beyond this milestone.

## Depends on

- [Topological triples and their maps](../../simplicial-and-singular/relative-homology/topological-triple.md)
- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Sources

- [Hatcher §2.1, Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

---
article_id: af_8d17f4be9605a1e8324a99fb
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Simplex.zeroFacePair_homologyMap_isIso
---

# The zero face induces an isomorphism in relative homology

For every `n : ℕ`, prove that the canonical zero-face map induces an isomorphism

`H_n(Δ[n], ∂Δ[n];R) ≅ H_n(∂Δ[n+1], Λ⁰[n+1];R)`.

The main artifact is
`Hatcher.Simplex.zeroFacePair_homologyMap_isIso`, stated for every homological
degree for which the canonical pair map is an isomorphism. For `n > 0`, use
the good-pair comparisons and the exact point-quotient isomorphism. Handle
`n = 0` directly: the source boundary is empty, so Proposition 2.22's local
`GoodPairData` interface does not apply. The direct branch must still prove
that the canonical map, rather than an arbitrary conjugate, is an isomorphism.

Formalized in `Hatcher/Singular/StandardSimplexZeroFaceHomology.lean` for an
arbitrary coefficient object in an abelian category with the required
coproducts, and for every simplex dimension and homological degree. In positive
simplex dimensions, naturality of the good-pair quotient comparison conjugates
the canonical relative-homology map to the reduced-homology map induced by
`zeroFacePointQuotientIso`; the theorem identifying that isomorphism's forward
map ensures this is the exact zero-face map. In dimension zero, the two endpoint
subspaces form an open binary cover of `∂Δ[1]`. The canonical pair map factors
as a source pair isomorphism, the binary-cover excision map, and a target pair
isomorphism, so this exceptional branch also proves that exact map is an
isomorphism.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)

## Proof depends on

- [Standard-simplex boundary and horn pairs are good](standard-simplex-boundary-good-pairs.md)
- [The zero face identifies the two simplex point quotients](standard-simplex-zero-face-point-quotient.md)
- [Good-pair relative homology is reduced quotient homology](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-relative-homology.md)
- [The good-pair quotient comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-quotient-comparison-naturality.md)
- [Binary-cover excision induces an isomorphism on relative homology](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.1, second isomorphism in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

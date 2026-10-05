---
article_id: af_34760c1b3ece607058533faf
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Simplex.doubleSimplexFirstPair_homologyMap_isIso
---

# The first simplex computes homology relative to the second

Let `D_n` be the double-simplex space and let its second simplex be the
distinguished subspace. Construct a collar neighborhood showing that this
second summand forms a good pair with `D_n`. Define the canonical map of pairs

`(Δ[n], ∂Δ[n]) ⟶ (D_n, Δ[n]_2)`

whose ambient component is the first pushout inclusion and whose subspace
component is the common boundary viewed in the second simplex.

The main theorem
`Hatcher.Simplex.doubleSimplexFirstPair_homologyMap_isIso` says that this
canonical map induces an isomorphism on relative homology in every degree.
For positive dimension, identify its point-quotient map by pushout pasting and
apply Proposition 2.22. Treat dimension zero directly, since the source
subspace is empty and hence is not accepted by the project's `GoodPairData`.

## Depends on

- [The ordered difference of the two simplices is a cycle](double-simplex-fundamental-cycle.md)

## Proof depends on

- [Standard-simplex boundary and horn pairs are good](standard-simplex-boundary-good-pairs.md)
- [The zero face identifies the two simplex point quotients](standard-simplex-zero-face-point-quotient.md)
- [Good-pair relative homology is reduced quotient homology](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-relative-homology.md)
- [The good-pair quotient comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-quotient-comparison-naturality.md)

## Sources

- [Hatcher §2.1, relative comparison in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

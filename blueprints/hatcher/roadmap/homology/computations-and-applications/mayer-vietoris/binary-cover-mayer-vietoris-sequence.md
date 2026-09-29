---
article_id: af_e0f7b901ba3a7f5ceb5ea0d6
source_units: [hatcher-2-2-mayer-vietoris]
declaration: theorem
origin: cited
---

# The binary-cover Mayer–Vietoris sequence

Let `A B : Set X` satisfy `Hatcher.Excision.CoverCondition A B`. For every
pair of adjacent degrees `m + 1 = n`, the canonical sequence

`H_n(A ∩ B;R) → H_n(A;R) ⊞ H_n(B;R) → H_n(X;R)`
`→ H_m(A ∩ B;R) → H_m(A;R) ⊞ H_m(B;R) → H_m(X;R)`

is exact. The first map is `(i_A*, -i_B*)`, the second is the sum of the two
inclusion-induced maps, and the third is the Mayer–Vietoris connecting map.
The degree-zero map `H_0(A;R) ⊞ H_0(B;R) → H_0(X;R)` is an epimorphism.

The main theorem is `Hatcher.MayerVietoris.sequence_exact`. Supporting public
declarations are `intersectionMap`, `unionMap`, `connecting`, `sequence`, and
`unionMap_zero_epi`. Construct an isomorphism from the generic homology
sequence of the chain short complex to this source-facing sequence. Use the
additivity of the homology functor for the middle term and the homology
isomorphism induced by the small-chain homotopy equivalence for the ambient
term.

Also record `Hatcher.MayerVietoris.connecting_eq`: if a small representative
of a class is written `z = x+y`, with `x` supported in `A` and `y` supported
in `B`, then its image under the connecting map is represented by
`∂x=-∂y` in `A ∩ B`. A coefficient-general generalized-element formulation,
parallel to `Hatcher.Relative.pairConnecting_eq`, is acceptable.

## Depends on

- [Binary-cover chains form a short exact sequence](binary-cover-chain-short-exact-sequence.md)
- [The binary-cover excision chain map is a homotopy equivalence](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-chain-equivalence.md)

## Proof depends on

- [Small singular chains include by a chain-homotopy equivalence](../../simplicial-and-singular/relative-homology/small-chains-and-excision/small-chain-inclusion-homotopy-equivalence.md)
- [A short exact sequence gives an exact homology sequence](../../simplicial-and-singular/relative-homology/short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.2, ordinary Mayer–Vietoris sequence and connecting map, pages 149–150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

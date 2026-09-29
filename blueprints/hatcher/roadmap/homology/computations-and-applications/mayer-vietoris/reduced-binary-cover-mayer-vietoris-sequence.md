---
article_id: af_e4422275f900824fc877374c
source_units: [hatcher-2-2-mayer-vietoris]
declaration: theorem
origin: cited
---

# The reduced binary-cover Mayer–Vietoris sequence

Let `A B : Set X` satisfy `Hatcher.Excision.CoverCondition A B`. For adjacent
degrees `m + 1 = n`, the sequence

`H̃_n(A ∩ B;R) → H̃_n(A;R) ⊞ H̃_n(B;R) → H̃_n(X;R)`
`→ H̃_m(A ∩ B;R) → H̃_m(A;R) ⊞ H̃_m(B;R) → H̃_m(X;R)`

is exact, with the same inclusion maps and signs as the ordinary sequence.
The connecting morphism is induced by the augmented chain short complex.

The main theorem is `Hatcher.MayerVietoris.reducedSequence_exact`.
Supporting declarations should include `reducedIntersectionMap`,
`reducedUnionMap`, `reducedConnecting`, and `reducedSequence`. Transport the
generic augmented homology sequence using the augmented small-chain
homotopy equivalence and the additive homology functor's biproduct
comparison.

If `A ∩ B` is nonempty, also define the terminal sequence

`H̃_0(A ∩ B;R) → H̃_0(A;R) ⊞ H̃_0(B;R) → H̃_0(X;R) → 0`

and prove `Hatcher.MayerVietoris.reducedZeroSequence_exact`. Package the
adjacent windows and terminal statement as
`Hatcher.MayerVietoris.reducedLongExact`. The nonemptiness hypothesis is
essential for this source-facing endpoint: without it, augmented degree-zero
homology records the suppressed degree-minus-one term.

## Depends on

- [Augmented binary-cover chains form a short exact sequence](augmented-binary-cover-chain-short-exact-sequence.md)
- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [Small augmented chains include by a chain-homotopy equivalence](small-augmented-chain-inclusion-homotopy-equivalence.md)
- [A short exact sequence gives an exact homology sequence](../../simplicial-and-singular/relative-homology/short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.2, reduced Mayer–Vietoris sequence, page 150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

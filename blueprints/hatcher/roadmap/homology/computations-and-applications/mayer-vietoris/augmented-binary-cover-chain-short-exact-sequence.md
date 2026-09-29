---
article_id: af_f479ae58dad58fcf6864ebc2
source_units: [hatcher-2-2-mayer-vietoris]
declaration: theorem
origin: cited
lean: Hatcher.MayerVietoris.augmentedChainComplexShortComplex_shortExact
statement: formalized
proof: formalized
---

# Augmented binary-cover chains form a short exact sequence

For arbitrary subsets `A B : Set X`, augment the binary-cover chain short
complex. Its successor degrees are the ordinary Mayer–Vietoris chain
sequence, while its inserted coefficient degree is

`0 → R → R ⊞ R → R → 0`,

with maps `(𝟙_R,-𝟙_R)` and codiagonal addition. The resulting short complex
of augmented chain complexes is short exact.

The main theorem is
`Hatcher.MayerVietoris.augmentedChainComplexShortComplex_shortExact`.
The supporting declarations `augmentedChainComplexIntersectionMap` and
`augmentedChainComplexUnionMap` have the displayed signed and codiagonal
components in degree zero and reuse the ordinary maps in every successor
degree. They form `augmentedChainComplexShortComplex`.

The middle complex augments the ordinary biproduct of the two member chain
complexes by their componentwise augmentations. Short exactness is proved
degreewise: the inserted coefficient sequence has the explicit splitting
with retraction `biprod.fst` and section `biprod.inr`, while each successor
degree is the corresponding evaluation of the ordinary short exact
Mayer–Vietoris chain complex.

For later passage to reduced homology,
`Hatcher.MayerVietoris.augmentedSubspaceChainIso` identifies the augmented
singular chains of a subspace with the corresponding supported-chain
complex, naturally for subset inclusions, and
`Hatcher.MayerVietoris.augmentedMiddleChainsIso` identifies the custom middle
term with the biproduct of the two singly augmented member complexes.

## Depends on

- [The binary-cover Mayer–Vietoris chain complex](binary-cover-chain-complex.md)
- [Small augmented chains include by a chain-homotopy equivalence](small-augmented-chain-inclusion-homotopy-equivalence.md)
- [The augmented singular chain complex](../../simplicial-and-singular/relative-homology/augmented-singular-chain-complex.md)

## Proof depends on

- [Binary-cover chains form a short exact sequence](binary-cover-chain-short-exact-sequence.md)

## Sources

- [Hatcher §2.2, augmented Mayer–Vietoris chain sequence, page 150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

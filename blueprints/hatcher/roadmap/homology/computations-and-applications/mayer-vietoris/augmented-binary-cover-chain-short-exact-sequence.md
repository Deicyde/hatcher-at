---
article_id: af_f479ae58dad58fcf6864ebc2
source_units: [hatcher-2-2-mayer-vietoris]
declaration: theorem
origin: cited
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
Supporting declarations should name the augmented intersection and union
maps and `augmentedChainComplexShortComplex`. Prove short exactness
degreewise: use the explicit split sequence above in degree zero and the
ordinary binary-cover splitting in every successor degree.

## Depends on

- [The binary-cover Mayer–Vietoris chain complex](binary-cover-chain-complex.md)
- [Small augmented chains include by a chain-homotopy equivalence](small-augmented-chain-inclusion-homotopy-equivalence.md)
- [The augmented singular chain complex](../../simplicial-and-singular/relative-homology/augmented-singular-chain-complex.md)

## Proof depends on

- [Binary-cover chains form a short exact sequence](binary-cover-chain-short-exact-sequence.md)

## Sources

- [Hatcher §2.2, augmented Mayer–Vietoris chain sequence, page 150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

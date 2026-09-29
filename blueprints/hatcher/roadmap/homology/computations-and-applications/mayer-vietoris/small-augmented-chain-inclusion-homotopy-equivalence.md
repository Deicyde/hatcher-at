---
article_id: af_f11bd43beef6f83e595364c2
source_units: [hatcher-2-2-mayer-vietoris]
declaration: def
origin: bridged
---

# Small augmented chains include by a chain-homotopy equivalence

For any family of subsets, augment the small singular chain complex by
restricting the ordinary singular-chain augmentation. When the interiors of
the family cover `X`, the canonical inclusion into the augmented singular
chain complex of `X` is a chain-homotopy equivalence.

The main artifact is
`Hatcher.Excision.smallAugmentedChainInclusionHomotopyEquiv`. Supporting
declarations should expose `smallAugmentedChainComplex` and its canonical
inclusion without a cover hypothesis. Under `SmallSimplicesCondition`, shift
the existing small-chain homotopy equivalence through `ChainComplex.augment`,
use the identity on the inserted coefficient object, and verify the
augmentation compatibility. The fact that every vertex is small for an
interior cover supplies the degree-zero identity.

This is project bridge infrastructure rather than a separately stated result
of Hatcher. It connects the formalized Proposition 2.21 to Hatcher's
instruction to augment the Mayer–Vietoris chain sequence.

## Depends on

- [The augmented singular chain complex](../../simplicial-and-singular/relative-homology/augmented-singular-chain-complex.md)
- [Small singular chains include by a chain-homotopy equivalence](../../simplicial-and-singular/relative-homology/small-chains-and-excision/small-chain-inclusion-homotopy-equivalence.md)

## Sources

- [Hatcher §2.2, augmented Mayer–Vietoris construction, page 150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

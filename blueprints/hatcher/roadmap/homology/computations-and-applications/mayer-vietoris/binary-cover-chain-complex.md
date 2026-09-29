---
article_id: af_d14323e64adefa9370c7e101
source_units: [hatcher-2-2-mayer-vietoris]
declaration: def
origin: cited
---

# The binary-cover Mayer–Vietoris chain complex

For subsets `A B : Set X` and coefficients `R`, let
`C_*^{A+B}(X;R)` be the chain complex of the simplicial subcomplex generated
by singular simplices whose images lie in `A` or in `B`. Construct the short
complex

`C_*(A ∩ B;R) → C_*(A;R) ⊞ C_*(B;R) → C_*^{A+B}(X;R)`.

The first map is the biproduct lift of the two inclusion-induced chain maps,
with the source convention `x ↦ (x,-x)`. The second is the biproduct descent
of the two canonical maps into the small-cover complex, so it acts as
`(x,y) ↦ x+y`. Their composite is zero.

The main artifact is
`Hatcher.MayerVietoris.chainComplexShortComplex`. Supporting declarations
should expose `smallCoverChains` and the canonical maps from the intersection
to each member and from each member to the small-cover complex. The
construction is defined for arbitrary `A` and `B`; the interior-cover
hypothesis is needed only when comparing small-cover homology with the
homology of `X`.

## Depends on

- [The singular chain complex](../../simplicial-and-singular/singular-chain-complex.md)
- [Iterated subdivision eventually makes every singular simplex small](../../simplicial-and-singular/relative-homology/small-chains-and-excision/eventually-small-singular-simplices.md)

## Sources

- [Hatcher §2.2, chain-level Mayer–Vietoris construction, pages 149–150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

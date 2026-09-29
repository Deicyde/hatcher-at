---
article_id: af_c930cb570baa902b5242a221
source_units: [hatcher-2-2-mayer-vietoris]
declaration: theorem
origin: cited
lean: Hatcher.MayerVietoris.chainComplexShortComplex_shortExact
statement: formalized
proof: formalized
---

# Binary-cover chains form a short exact sequence

For arbitrary subsets `A B : Set X`, the Mayer–Vietoris chain complex is
short exact:

`0 → C_*(A ∩ B;R) → C_*(A;R) ⊞ C_*(B;R)`
`→ C_*^{A+B}(X;R) → 0`.

The main theorem is
`Hatcher.MayerVietoris.chainComplexShortComplex_shortExact`. Its proof maps
the simplicial-set pushout square for the binary small-cover subcomplex
through the singular-chain functor. Pushout exactness supplies exactness and
epimorphy, while projection onto the `A` component proves that the signed
intersection map is monic. This categorical argument is the coproduct-basis
splitting in invariant form and preserves the source signs from the preceding
node.

Use a coefficient-general abelian category with the coproducts required by
singular chains. The proof may adapt the `Sigma`-basis splitting technique
used in relative dévissage, but the theorem must concern the canonical maps
defined in the preceding node.

## Depends on

- [The binary-cover Mayer–Vietoris chain complex](binary-cover-chain-complex.md)

## Sources

- [Hatcher §2.2, exactness of the binary-cover chain sequence, pages 149–150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)

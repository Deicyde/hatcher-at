---
article_id: af_e9f8e873d37465155412edda
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# Relative homology commutes with coproducts of arbitrary pairs

Assume the coefficient category has exact coproducts of the size of `ι`, via
Mathlib's `AB4OfSize` interface. Construct

`∐ i, H_k(P i; R) ≅ H_k(sigmaPair P; R)`.

The main artifact is `Hatcher.Relative.relativeHomologySigmaPairIso`. Its
forward map must satisfy the component formula

`Sigma.ι _ i ≫ iso.hom = H_k(sigmaPairι P i)`.

The existing pointed-pair isomorphism remains available as a specialization.
The integral finite-family instance used by Proposition 2.30 must require no
additional hypotheses at call sites.

## Depends on

- [Relative chains commute with coproducts of arbitrary pairs](relative-chains-sigma-pair.md)
- [Relative homology commutes with exact coproducts](../post-excision-applications/relative-homology-coproduct.md)

## Sources

- [Hatcher §2.2, direct-sum step in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)

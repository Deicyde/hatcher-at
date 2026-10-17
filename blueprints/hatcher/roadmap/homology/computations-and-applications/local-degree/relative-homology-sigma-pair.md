---
article_id: af_e9f8e873d37465155412edda
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.relativeHomologySigmaPairIso
---

# Relative homology commutes with coproducts of arbitrary pairs

Assume the coefficient category has exact coproducts of the size of `ι`, via
Mathlib's `AB4OfSize` interface. Construct

`∐ i, H_k(P i; R) ≅ H_k(sigmaPair P; R)`.

The main artifact is `Hatcher.Relative.relativeHomologySigmaPairIso`. Its
forward map must satisfy the component formula

`Sigma.ι _ i ≫ iso.hom = H_k(sigmaPairι P i)`.

Expose the underlying canonical map as
`Hatcher.Relative.relativeHomologySigmaPairMap`, identify the isomorphism's
forward morphism with it, and name the component theorem
`Hatcher.Relative.ι_relativeHomologySigmaPairIso_hom`. Also provide
`Hatcher.Relative.relativeIntegralHomologySigmaPairIso` for universe-zero
integral pairs with no extra call-site hypotheses.

Make every existing pointed map, isomorphism, component theorem, and integral
isomorphism an exact compatibility specialization rather than a parallel
proof.
The integral finite-family instance used by Proposition 2.30 must require no
additional hypotheses at call sites. Preserve the empty-index case and use the
same universe for `ι` and the family of topological pairs, matching the chain
API.

## Depends on

- [Relative chains commute with coproducts of arbitrary pairs](relative-chains-sigma-pair.md)
- [Relative homology commutes with exact coproducts](../post-excision-applications/relative-homology-coproduct.md)

## Sources

- [Hatcher §2.2, direct-sum step in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)

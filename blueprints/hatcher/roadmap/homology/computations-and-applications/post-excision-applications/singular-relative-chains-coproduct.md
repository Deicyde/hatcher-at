---
article_id: af_8204b616ad8eafa934bae57a
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
lean: Hatcher.Relative.relativeChainComplexSigmaIso
statement: formalized
proof: formalized
---

# Relative singular chains commute with topological coproducts

Construct a chain-complex isomorphism from the categorical coproduct of the
relative singular chain complexes of a family of pairs to the relative chain
complex of their sigma pair. Specialize the public interface to the family of
pointed pairs used for wedge sums:

`∐ i, C_*(X_i,{x_i};R) ≅ C_*(Σ i, X_i; Σ i,{x_i};R)`.

Its component on every
summand must be the chain map induced by the canonical sigma inclusion.

Use `ContinuousMap.sigmaCodHomeomorph`: the topological standard simplex is
connected, so every singular simplex in a disjoint union lands in one unique
summand. Prove that this equivalence commutes with every face map and hence
with the alternating differential.

## Depends on

- [The coproduct pair of a family of pointed spaces](sigma-pointed-pair.md)
- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Sources

- [Hatcher §2.1, coproduct step in Corollary 2.25, printed page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

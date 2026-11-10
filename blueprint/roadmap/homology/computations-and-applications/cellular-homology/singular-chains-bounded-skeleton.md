---
article_id: af_401e1c6dfdf6e37cba588880
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.singularChain_exists_boundedSkeletonLift, Hatcher.ClassicalCW.singularSkeletonInclusion, Hatcher.ClassicalCW.singularSkeletonChainMap, Hatcher.ClassicalCW.singularSkeletonChainMap_injective, Hatcher.ClassicalCW.singularSkeletonChainMap_boundary_iff, Hatcher.ClassicalCW.singularSkeletonChainMap_cycle_iff
---

# Finite families of singular chains lift to one skeleton

For any classical CW complex X, a finite family of actual integral singular
chains of any fixed degree lifts through inclusion from one common finite
skeleton, with the bound at least any prescribed bound. The inclusion chain
maps are injective in every degree and reflect cycle and boundary equations
for these lifts. An empty family admits the prescribed bound. No bound on
the dimension or number of cells of X is assumed.

## Proof sketch

A chain has finite support in continuous standard simplices. Their images
form a compact subset, so the compact-subset theorem places them in one
skeleton. Restrict supported simplices to that skeleton and keep their
coefficients. Injectivity on simplices gives injectivity on free chain
groups and reflects the differential equations.

## Depends on

- [Singular chain complex](../../simplicial-and-singular/singular-chain-complex.md)

## Proof depends on

- [Compact subset bounded skeleton](../../../appendix/classical-cw-bridge/compact-subset-bounded-skeleton.md)
- [Singular relative chains coproduct](../post-excision-applications/singular-relative-chains-coproduct.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)

---
article_id: af_e709207d0f23c61c8259719f
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
---

# Relative singular chains and homology

**Hatcher, §2.1 (pages 115–118).** For a topological pair `(X,A)`, define
relative singular chains as `Cₙ(X;R) / Cₙ(A;R)` and relative singular
homology as their homology. A map of pairs induces the corresponding map on
relative chains and homology.

The main artifact should be `Hatcher.Relative.homologyFunctor`; supporting
artifacts include `Hatcher.Relative.chainComplexFunctor` and the quotient map
from absolute chains. Supporting lemmas characterize relative cycles as chains
whose boundary lies in the subspace chain complex, and relative boundaries as
classes represented by an absolute boundary modulo a subspace chain. These
definitions are obtained by composing the topological singular-pair functor
with Mathlib's `SSetPair` functors.

## Depends on

- [The singular set of a topological pair](singular-pair-functor.md)
- [Singular homology](../singular-homology.md)

## Sources

- [Hatcher §2.1, relative homology and induced maps, pages 115–118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)

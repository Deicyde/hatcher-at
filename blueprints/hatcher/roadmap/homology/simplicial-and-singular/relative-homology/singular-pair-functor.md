---
article_id: af_0a7e9a54781df8354811b9b7
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.singularPairFunctor
---

# The singular set of a topological pair

For a topological pair `P`, apply `TopCat.toSSet` to the embedding
`P.map : P.snd ⟶ P.fst` and prove the resulting simplicial map is a
monomorphism. This defines a functor from topological pairs to simplicial-set
pairs while preserving maps of pairs.

Formalized as
`Hatcher.Relative.singularPairFunctor : TopPair ⥤ SSetPair` in
`Hatcher/Singular/Relative.lean`. The direction respects the two APIs:
`TopPair.fst` is the ambient space and
`SSetPair.right` is the ambient simplicial set. Joël Riou's excision prototype
contains a compatible `TopPair.toSSetPair`, but it is implementation prior art,
not a pinned dependency.

## Depends on

- [Relative homology of a simplicial-set pair](simplicial-pair-relative-homology.md)

## Sources

- [Hatcher §2.1, topological pairs, pages 115–118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)

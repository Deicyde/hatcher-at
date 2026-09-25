---
article_id: af_cf02faa75ba81780b7cc01da
source_units: [hatcher-2-1-triple-les]
declaration: structure
origin: bridged
statement: formalized
lean: Hatcher.Relative.TopTriple
---

# Topological triples and their maps

For nested subspaces `B ⊆ A ⊆ X`, bundle the composable embeddings
`B ↪ A ↪ X` as a topological triple `(X,A,B)`. It determines the three
topological pairs `(A,B)`, `(X,B)`, and `(X,A)`, together with the canonical
maps of pairs

`(A,B) → (X,B) → (X,A)`.

Define a morphism of triples by compatible maps on all three spaces, and expose
the induced morphisms of these pairs. The main declaration is
`Hatcher.Relative.TopTriple`; its morphism and pair projections are supporting
definitions in the same review unit.

## Depends on

None.

## Sources

- [Hatcher §2.1, triples, pages 118–119 and maps of triples, page 128](../../../../sources/hatcher-2-1.md)
- [Triple-homology implementation specification](../../../../sources/triple-homology-implementation.md)

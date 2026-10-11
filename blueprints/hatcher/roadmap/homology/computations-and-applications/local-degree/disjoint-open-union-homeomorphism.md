---
article_id: af_23c4db77f1f2f28686db47cb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: background
---

# A disjoint open family is homeomorphic to its sigma type

Let `U : ι → Set X` be pairwise disjoint open subsets. Construct the canonical
homeomorphism

`(Σ i, U i) ≃ₜ ⋃ i, U i`

which forgets the summand tag. The main artifact is
`Hatcher.Topology.sigmaSubtypeHomeomorphUnion`. Its forward map and inverse on
a point lying in `U i` must have explicit computation lemmas.

The proof may use openness to show that the inverse is continuous and
pairwise disjointness to show the index is unique. Empty summands and an empty
index type remain valid.

## Depends on

None.

## Sources

- [Hatcher §2.2, disjoint neighborhoods in the local-degree construction, printed pages 135–136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)

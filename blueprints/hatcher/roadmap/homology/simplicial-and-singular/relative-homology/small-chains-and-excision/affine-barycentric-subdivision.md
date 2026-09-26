---
article_id: af_5d0836e3e923b63dbb7abb27
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Excision.affineSubdivisionIter_face
---

# Affine barycentric subdivision is compatible with faces

For an affine map from a real standard simplex into a convex space, define the
barycentric subsimplex indexed by a permutation of the vertices and its
iterates. The vertices are the images of barycenters of the nested faces in
the corresponding complete flag.

The main theorem, intended as
`Hatcher.Excision.affineSubdivisionIter_face`, says that every iterated
barycentric subdivision of a face is itself a face of an iterated barycentric
subdivision of the original affine simplex. The same review unit supplies the
single-step face identity and the permutation/sign bookkeeping later needed to
prove that subdivision commutes with the chain boundary.

These definitions are local compatibility scaffolding for Hatcher's geometric
construction, not a claim that the affine-simplex API is present at the pinned
Mathlib version.

## Depends on

None.

## Sources

- [Hatcher §2.1, barycentric subdivision of simplices, pages 119–121](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's affine-simplex implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/ConvexSpace/StdSimplex.lean)

---
article_id: af_63172729a78d73c830baa7d1
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.mappingCone
---

# The mapping cone of a topological pair

**Hatcher, §2.1 (page 125).** For a topological pair
`P : TopPair`, representing an embedding `P.map : P.snd ⟶ P.fst`, define its
mapping cone `X ∪ CA` by attaching the cone
`CA = (A × I) / (A × {0})` to `X` along the copy of `A` at height one.
The main declaration is

`Hatcher.Relative.mappingCone (P : TopPair.{w}) : TopCat.{w}`.

Use the existing explicit point-set model
`Hatcher.VanKampen.ConeAttachment P.map`: height zero is collapsed to its
distinguished apex, and height one is glued to `P.fst` through `P.map`. The
existing pushout theorem must witness that this is the topological mapping
cone, rather than an opaque homeomorphic replacement. Retain the explicit apex
when `P.snd` is empty; then the model is `P.fst ⊔ point`, which makes the
degree-zero reduced comparison in the final theorem valid without a
nonemptiness hypothesis.

In the same formalization unit, expose the standard two-set cover under the
relative-homology namespace. Define `mappingConeUpperPair P` to be the pair
whose subspace is the contractible `upperCover`, and define
`mappingConeCoverPair P` to be `(lowerCover, upperCover ∩ lowerCover)`.
Package the two open sets as `mappingConeCoverCondition P` with `upperCover`
as the first subset and `lowerCover` as the second. Finally define the
canonical excision morphism

`Hatcher.Relative.mappingConeExcision P :`
`  mappingConeCoverPair P ⟶ mappingConeUpperPair P`

to be `Hatcher.Excision.coverPairHom (mappingConeCoverCondition P)`. These
supporting definitions must retain the exact canonical inclusion used by the
existing binary-cover excision theorem. No mapping-cone functor or naturality
claim is part of this node.

## Depends on

- [A single cone attachment has a two-set open cover](../../../fundamental-group/van-kampen/cell-attachment-support/single-cone-open-cover.md)
- [Binary-cover excision is a chain-homotopy equivalence](../../simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-chain-equivalence.md)

## Proof depends on

- [A single cone attachment is a topological pushout](../../../fundamental-group/van-kampen/cell-attachment-support/single-cone-pushout.md)

## Sources

- [Hatcher §2.1, arbitrary-pair mapping-cone comparison, page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

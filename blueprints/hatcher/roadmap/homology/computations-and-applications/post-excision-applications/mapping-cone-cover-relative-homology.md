---
article_id: af_88908032037e3aad0cb5e672
source_units: [hatcher-2-1-post-excision-applications]
declaration: instance
origin: bridged
---

# The mapping-cone cover has the relative homology of the original pair

For `P : TopPair`, construct a morphism of topological pairs

`Hatcher.Relative.mappingConeCoverRetraction P :`
`  mappingConeCoverPair P ⟶ P`.

Its ambient component is the existing retraction from the mapping cone's
`lowerCover` to `P.fst`. Its subspace component is an explicit projection
`upperCover ∩ lowerCover ⟶ P.snd` obtained from the open interior cylinder.
The two components must commute strictly with the pair embeddings: on an
interior cylinder point represented by `(a,t)`, the ambient retraction is
`P.map a`, while the subspace projection is `a`.

The main declaration is the instance

`Hatcher.Relative.mappingConeCoverRetraction_homologyMap_isIso`

stating, for every coefficient object `R` in an abelian category with the
required coproducts and every `n : ℕ`, that

`IsIso ((Hatcher.Relative.homologyFunctor R n).map`
`  (Hatcher.Relative.mappingConeCoverRetraction P))`.

Expose a homotopy equivalence whose forward map is exactly the chosen
intersection projection. Do not rely on unfolding the opaque choice inside
the existing intersection equivalence. The ambient and subspace components
then induce ordinary homology isomorphisms, and the completed componentwise
relative-homology criterion supplies the stated instance, including degree
zero. This node does not assert a new homeomorphism or a homotopy equivalence
in the category `TopPair`.

## Depends on

- [The mapping cone of a topological pair](mapping-cone-model.md)
- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Proof depends on

- [The base-side cone cover retracts onto the original space](../../../fundamental-group/van-kampen/cell-attachment-support/single-cone-base-retract.md)
- [The single-cone cover intersection has the homotopy type of its boundary](../../../fundamental-group/van-kampen/cell-attachment-support/single-cone-intersection.md)
- [A homotopy equivalence induces homology isomorphisms](../../simplicial-and-singular/homotopy-equivalence-homology-iso.md)
- [Componentwise isomorphisms imply a relative isomorphism](../../simplicial-and-singular/relative-homology/good-pair-quotient/relative-homology-map-isomorphism-criterion.md)

## Sources

- [Hatcher §2.1, arbitrary-pair mapping-cone comparison, page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

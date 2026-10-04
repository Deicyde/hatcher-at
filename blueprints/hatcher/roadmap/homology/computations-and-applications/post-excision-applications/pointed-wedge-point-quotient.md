---
article_id: af_b3bfe8f0cd2aeab13b17a77d
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# The pointed wedge is the point quotient of the sigma pair

Identify the existing project model `Hatcher.PointedWedge X x₀` with the
point quotient of `sigmaPointedPair x₀`. Prove that the square from the sigma
of the chosen basepoints to the sigma of the spaces and to `PUnit` is a
pushout in `TopCat`, then construct

`Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge`.

The isomorphism must carry the quotient point to
`Hatcher.PointedWedge.basepoint x₀`, and the quotient projection restricted to
summand `i` to `Hatcher.PointedWedge.inclusion x₀ i`. Include these as public
simp lemmas so the final homology map can be identified with Hatcher's direct
sum of inclusion-induced maps.

The construction includes the empty family: the point quotient of the empty
pair and the project's empty wedge are both one-point spaces.

## Depends on

- [The coproduct pair of a family of pointed spaces](sigma-pointed-pair.md)
- [The pointed wedge of a family of spaces](../../../fundamental-group/van-kampen/pointed-wedge.md)
- [Functorial point quotients of topological pairs](../../simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-functor.md)

## Sources

- [Hatcher §2.1, quotient proof of Corollary 2.25, printed page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
